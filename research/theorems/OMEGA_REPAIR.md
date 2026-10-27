# Repairing Gómez's ΩH_q by relabelling the copies: geometric relabellings cannot work for q ≥ 8

Job thm-omega-repair (Opus, 27 October 2026), branch `claude/thm-omega-repair-m4luls`. Tools and logs:
`research/omega_repair/` (README there). Labels: **Theorem** (proved here by hand), **Computer-checked** (a statement
about finite data, with the check named), **Heuristic** (an argument with a named gap).

Background: Gómez's ΩH_q (thesis, UPC 1986, §2.9.3) has diameter ≥ 9 as defined, so the table entries (10,8), (11,8),
(12,8), (14,8), (15,8), (16,8) have no checkable diameter-8 graph (research/squads/cells/d12D8_table.md, Theorems 1–2, on
branch claude/own-12-8-cell-ig5jhd; confirmed by research/referee/omega-dq.md on claude/omega-dq-referee-bzzlid). Giving
each copy its own labelling reaches diameter 8 at q = 2 and q = 3 (claude/table-audit-2-p7x6hn,
research/projects/table-audit/omega/NOTES.md). This note asks which relabellings can work for larger q.

## Verdict

1. **Relabelling a copy by one collineation (the same on points and lines) changes nothing**: the graph is isomorphic to
   the thesis graph (Lemma 1.2). Relabelling by dualities only changes which colour class of a copy carries which hubs,
   which is the setting of Theorem 2 of d12D8_table.md (diameter ≥ 9 for q ≥ 7).
2. **Main result (Theorem 3.3).** Call a labelling *geometric* if every transfer map (the mark of a hub in one copy to
   its mark in another copy) is the restriction of an automorphism of the incidence graph of H(q): a collineation, or a
   duality when q = 3^e. This contains every "collineation coset" labelling, where copy c labels its points by
   a collineation a_c and its lines by a possibly different collineation b_c (the first rung above the thesis). **For
   every q ≥ 8 and every geometric labelling of Gómez's wiring (any mix of the two block types, reading 2 of the figures),
   ΩH_q has diameter ≥ 9.** For q = 8, 9, 11, 13 the same holds for every reading of the figures and every choice of
   inner classes, dualities included (Theorem 3.5). This covers every table entry except (10,8). The proof is a count:
   in a geometric labelling every route from a hub into a copy it misses reaches one ball of the hexagon, and Gómez's
   wiring gives some hub only α = ⌊(q+3)/2⌋ routes of length ≤ 7 into some copy, too few balls to cover it.
3. **Explicit far vertices.** In that pair, every hub (t, k) has at least q⁵ − αq⁴ − m₂q² vertices at distance ≥ 9 in
   the missed copy: at least 3,712 at q = 8, 3,726 at q = 9, 26,862 at q = 11 and 84,162 at q = 13 (Computer-checked 3.4).
4. **q ≤ 7.** The count is not enough (the bound is −1,764 at q = 7). At q = 7 it is enough under a general-position
   condition on one point t (Theorem 4.2), which we cannot prove holds for every labelling. Computer: geometric labellings
   are far worse than random arbitrary labellings at every q tested. Annealed geometric labellings leave 805 far pairs at
   q = 2, 259,169 at q = 3, 18.2 million at q = 4 and 209 million at q = 5, against about 70, 1,911, 646,000 and 6.6
   million for random arbitrary labellings. Annealing inside the class removes 10 % at q = 3 and under 2 % at q = 4, 5
   (Computer-checked 4.3).
5. **What is left.** A repair at q ≥ 4, if one exists, must use non-geometric labellings whose transfer maps scatter
   balls (§5). No counting argument excludes them (the audit's union bound stays near 3). We found no valid graph, so no
   builder is saved.

Answer to the brief: (b) is done for the natural class "π_c in Aut(H(q)) on points and on lines, independently" (and its
duality extension), for all q ≥ 8 and so for all table cells except (10,8). (a) found nothing: every structured family
tried (Singer powers, root elation groups, random twists, annealed twists) is worse than random. (c) is answered inside
the geometric class (items 3 and 4), not for general labellings.

## 1. Setting

### 1.1 The hexagon

H = H(q) is the split Cayley hexagon with point set P and line set L, N := |P| = |L| = (q⁶−1)/(q−1), I its incidence
graph (bipartite, (q+1)-regular, diameter 6, girth 12), d the distance in I, B(z, R) = {x : d(z,x) ≤ R} and
opp(t) = {x : d(t,x) = 6}. Points are the points of the parabolic quadric Q(6,q). Two points are at distance ≤ 4 in I if
and only if they are collinear in the polar space Q(6,q), that is, perpendicular for the polar form b
(Van Maldeghem, *Generalized Polygons*, 2.4.13). For a point x, B(x, 2) ∩ P is the totally singular plane π_x that
holds the q+1 hexagon lines through x, and B(x, 4) ∩ P = x^⊥ ∩ Q(6,q). Aut(I) consists of the collineations
(G₂(q) ⋊ Aut(F_q)) and, when q = 3^e, the dualities.

### 1.2 ΩH_q with a labelling of each copy

As in d12D8_table.md §1: α blocks of 5 copies (copy c = 5B + i, i ∈ Z₅), each block of type a or b, and hub classes k
and k̄ for k ∈ Z₅, each holding one hub per row t ∈ [N]:

- type a: (t,k) meets copies k−1, k+1; (t,k̄) meets copies k+2, k+3 of the block;
- type b: (t,k) meets copies k+3, k+4; (t,k̄) meets copies k−1, k+1.

Δ₁ + 2 = q + 3 = 2α + β, so there are 5α copies and every hub has degree 2α. In **reading 2** the unbarred hubs sit on
points and the barred hubs on lines in every copy. In reading 1 the inner dots are lines in every block. The table
audit's model allows an arbitrary inner class per block. A **labelling** gives each copy c bijections
P_c: [N] → P and L_c: [N] → L. Hub (t,k) is joined to the mark of row t, of its class's colour, in each copy it meets.
The thesis's labelling is P_c = P₀, L_c = L₀ for all c. For a hub class Y meeting copies c and d, the **transfer**
T_Y(c→d) maps the mark of row t in c to the mark of row t in d, so T = L_d L_c⁻¹, P_d P_c⁻¹, L_d P_c⁻¹ or P_d L_c⁻¹.

**Definition.** A labelling is *geometric* if every transfer is the restriction of an element of Aut(I). It is
*twisted* (a "collineation coset" labelling) if P_c = a_c P₀ and L_c = b_c L₀ with collineations a_c, b_c. Twisted
labellings are geometric in reading 2. In reading 1 a geometric labelling needs L₀P₀⁻¹ to be the restriction of a
duality, so it exists only for q = 3^e.

**Lemma 1.1 (Theorem; normal form).** A twisted labelling gives a graph isomorphic to the one in which copy c labels its
points by P₀ = (the identity on rows = points) and its lines by λ_c ∘ L₀, with λ_c = a_c⁻¹ b_c. After renaming the rows
of the barred hubs, P-hub (t,k) sits on point t of every copy it meets and L-hub (m,k̄) on line λ_c(m) of copy c.

*Proof.* Apply a_c⁻¹ to copy c. It is an automorphism of the copy, and it maps P_c to P₀ and L_c to a_c⁻¹b_c L₀.
Renaming barred rows by L₀ changes no adjacency. ∎

**Lemma 1.2 (Theorem; the first rung).** If every copy is relabelled by one collineation g_c (a_c = b_c = g_c), the
graph is isomorphic to the thesis graph (all λ_c = id), so its diameter is ≥ 9 (Theorem 1 of d12D8_table.md in reading 2;
Theorem 2 there in the mixed readings, q ≥ 7). If copy c is relabelled by a duality δ_c (points to lines), applying
δ_c⁻¹ to the copy gives back the thesis's labels with the point and line roles of that copy exchanged. This is a change
of inner and outer class in copy c, the setting of Theorem 2 there.

*Proof.* Lemma 1.1 with λ_c = id. For a duality, δ_c⁻¹ is an isomorphism from the copy to I with its colour classes
exchanged. ∎

## 2. Routes reach balls

From here on, unless said otherwise: reading 2, a twisted labelling in the normal form of Lemma 1.1, and λ acting on
points through its induced collineation.

**Lemma 2.1 (Theorem; routes).** Let h = (t,k) be a P-hub and c' a copy it misses (c' ∉ C(k)). Every point of c' at
distance ≤ 7 from h lies in

  B(t, 4) ∪ ⋃_{c₁ ∈ N(k,c')} B(λ_{c'}λ_{c₁}⁻¹(t), 4) ∪ ⋃_{z ∈ Z₂} B(z, 2),

where N(k,c') is the set of copies c₁ ∈ C(k) that share a barred class with c', and Z₂ = A ∪ B with
A = {λ_{c'}λ_b⁻¹(t) : b ≠ c'} and B = {λ_{c₂}λ_{c₁}⁻¹(t) : c₁ ∈ C(k), c₂ ≠ c₁ shares a barred class with c₁}.
The same holds for an L-hub (m, k̄) and the lines of a copy it misses, with points and lines exchanged and λ replaced by
λ⁻¹ (apply λ_c⁻¹ to every copy c to untwist the lines).

*Proof.* A path from h to v ∈ c' leaves h to its mark t in a copy c₁ ∈ C(k), then alternates walks inside copies with
passes copy → hub → copy (2 edges). A hub meets a copy once, so consecutive copies differ, and c' ≠ c₁. With r copies
visited and segments of lengths a₁, …, a_r, the length is 1 + Σaᵢ + 2(r−1) ≤ 7, so r ≤ 4 and Σaᵢ ≤ 8 − 2r. A pass
through a P-hub keeps the point index (P-hubs sit on the same point in every copy). A pass through an L-hub from copy c
to copy d maps line λ_c(m) to λ_d(m), that is, applies λ_dλ_c⁻¹. Both are collineations, so they commute with balls:
by induction the endpoint lies in B(g(t), Σaᵢ), where g is the product of the passes. Parities: the walk starts and ends
at points, so a segment before an L-pass is odd and Σaᵢ is even. Cases:
- r = 2 (Σaᵢ ≤ 4): a P-pass gives g = id; an L-pass needs a barred class meeting c₁ and c', and gives λ_{c'}λ_{c₁}⁻¹.
- r = 3 (Σaᵢ ≤ 2): P then P gives id. P then L forces a₁ = 0, a₂ = a₃ = 1 and g = λ_{c'}λ_{c₂}⁻¹ (in A). L then P
  forces a₁ = a₂ = 1, a₃ = 0 and g = λ_{c₂}λ_{c₁}⁻¹ with c₂ sharing a barred class with c₁ (in B). L then L forces a₂ = 0
  and gives λ_{c'}λ_{c₂}⁻¹λ_{c₂}λ_{c₁}⁻¹ = λ_{c'}λ_{c₁}⁻¹ (in A).
- r = 4: every aᵢ = 0, so every pass is at a point: g = id, radius 0. ∎

**Computer-checked 2.2.** The exact union of the route balls (`twist.c formula`, which enumerates the routes rather than
the families above) equals the far-pair count of a plain BFS on the explicit graph (`twist.c bfs`) for the thesis
labelling and random twists at q = 2 (pattern ab) and q = 3 (aba, aab). It also equals the count of the table audit's
independent builder and BFS (`check/omega_eval`, copied unchanged from claude/table-audit-2-p7x6hn) at q = 3 (288,846)
and q = 4 (18,464,523). BFS from all vertices gives exactly twice the hub-source count, so in these graphs every far
pair is a (hub, missed-copy vertex) pair. Logs: `logs/formula_vs_bfs.txt`, `logs/audit_crosscheck.txt`.

**Lemma 2.3 (Theorem; only hub-to-missed-copy pairs matter).** In reading 2 with both block types present, under any
twisted labelling, every pair of vertices other than (hub, vertex of a copy the hub misses at odd distance) is at
distance ≤ 8.

*Proof.* (i) Any two copies share a hub class: in one block or two blocks of the same type, the class sets
{i±1 | i+2, i+3} (type a) and {i+1, i+2 | i±1} (type b) of copies at positions i, i' meet for every i − i' ∈ Z₅, and an a-copy
and a b-copy share an unbarred class unless i − i' = 4, when they share a barred one. So a line ℓ of c and a point v of
c' are joined by ℓ → (a point or ℓ itself) → shared hub → c' and then ≤ 5 or ≤ 4 steps. The transfer is a collineation,
so the image of the pencil of ℓ or of ℓ itself is within distance 5 of every point. Total ≤ 7. (ii) P-hub (t,k) and
L-hub (m,j̄) share a copy (in an a-block unless j = k, in a b-block unless k − j = 3), where they are joined through a
point–line distance ≤ 5: total ≤ 7. Two hubs of one bar share a copy, total ≤ 8. (iii) A P-hub (t,k) and a line of a missed copy c':
by (i) some c₁ ∈ C(k) shares a class Y ≠ k with c'. If Y is unbarred: t → hub (t,Y) → point t of c' → ≤ 5 steps,
total 8. If Y is barred: one step to a line through t, a pass to the pencil of the point λ_{c'}λ_{c₁}⁻¹(t), then ≤ 4
steps (every line is within 5 of that point); total 8. L-hubs are symmetric. ∎

So for twisted labellings in reading 2, **diameter 8 ⟺ every hub reaches every opposite-colour vertex of every copy
it misses within 7 steps**, and Lemma 2.1 lists the balls that must cover the copy.

**Lemma 2.4 (Theorem; geometric labellings, any reading).** For any geometric labelling, any reading and any inner
classes, the vertices of a missed copy c' within distance 7 of a hub are a union of balls B(W(x₀), R), one for each route,
where W is a freely reduced word in the labelling automorphisms and in δ (Lemma 1.1's normal form with
P_c = a_cP₀, L_c = b_cL₀, L₀P₀⁻¹ = δ|_P), and R is the largest admissible total segment length. The centre has the target
type if and only if R is even.

*Proof.* As for Lemma 2.1: each transfer is the restriction of an automorphism of I, so it commutes with balls. ∎

## 3. The counting theorem

**Lemma 3.1 (Theorem; constants).** Let t, z be distinct vertices of I of the same type. Then |B(z,4) ∩ opp(t)| = q⁴,
and |B(z,2) ∩ opp(t)| is 0 if d(t,z) = 2 and q² otherwise. If z has the other type, |B(z,3) ∩ opp(t)| ∈ {0, q³} and
|B(z,1) ∩ opp(t)| ∈ {0, q}.

*Proof.* For points of H(q): B(z,4) ∩ P = z^⊥ ∩ Q has 1 + q(q³+q²+q+1) points, and B(z,4) ∩ B(t,4) ∩ P is the set of
points of Q(6,q) collinear (in the polar space) with z and t, which has q³+q²+q+1 points whether z, t are collinear
(a cone over a conic with a line as vertex) or not (a Q(4,q)). The difference is q⁴. For B(z,2): each hexagon line
through z has exactly one point at distance ≤ 4 from t when d(t,z) ≥ 4, except the one line towards t when
d(t,z) = 4, which lies inside B(t,4). Counting gives 1 + (q+1)(q−1) = q² when d(t,z) = 6 and q·q = q² when
d(t,z) = 4. If d(t,z) = 2, every point within distance 2 of z is within distance 4 of t. For lines, use that the
collinearity graph of a generalized hexagon of order (s,t) is distance-regular with intersection numbers depending only
on (s,t), and the dual hexagon also has order (q,q). The odd radii (used only in Theorem 3.5) are taken from Computer-checked 3.1′. ∎

**Computer-checked 3.1′.** All these values, for every distance d(t,z), from points and from lines, on H(3), H(4), H(5)
and H(7) (`counts.c`, log `logs/counts.txt`).

**Lemma 3.2 (Theorem; a starved pair).** For every block pattern there is an unbarred class k and a copy c' ∉ C(k) with
|N(k,c')| = α: exactly one copy per block reaches c' by one L-pass.

*Proof.* A copy at position i has barred classes {i+2, i+3} (type a) or {i−1, i+1} (type b). If some block has type a,
take c' at position k+3 in it (c' ∉ C(k) = {k±1}). Its barred classes are {k, k+1}. In an a-block, C(k) = {k−1, k+1}
with barred classes {k+1, k+2} and {k+3, k+4}: one shares. In a b-block, C(k) = {k+3, k+4} with barred classes
{k+2, k+4} and {k+3, k}: one shares. If every block has type b, take c' at position k (barred {k−1, k+1}), and the same
check gives one copy per block. ∎

**Theorem 3.3.** Let q ≥ 8. For every block pattern (any number of a- and b-blocks) and every twisted labelling (reading
2), and more generally every geometric labelling in reading 2, ΩH_q has diameter ≥ 9. For the pair (k, c') of
Lemma 3.2, every hub (t,k) has at least q⁵ − αq⁴ − m₂q² > 0 vertices of c' at distance ≥ 9, where m₂ is the number of
distinct radius-2 centres (m₂ ≤ 8α² − 1).

*Proof.* By Lemma 2.1, the points of c' within distance 7 of (t,k) are covered by B(t,4) (which misses opp(t)), by the
α balls B(λ_{c'}λ_{c₁}⁻¹(t), 4), c₁ ∈ N(k,c') (each meets opp(t) in ≤ q⁴ points, Lemma 3.1, and in 0 if the centre is t),
and by the radius-2 balls around Z₂ (≤ q² each). Family A has at most 5α − 1 − α = 4α − 1 members besides the radius-4
centres. Family B has at most 2α · 2(2α − 1) members: each copy has two barred classes, each meeting 2α copies. So
m₂ ≤ 8α² − 1, and

  |opp(t) ∖ covered| ≥ q⁵ − αq⁴ − (8α² − 1)q².

This is positive when q²(q − α) ≥ 8α². With α ≤ (q+3)/2 it suffices that q²(q − 3) ≥ 4(q+3)², which holds for q = 10
(700 ≥ 676) and, the left side growing faster, for all q ≥ 10. For q = 8, 9 the exact m₂ of the best pair is used
(Computer-checked 3.4): the bound is ≥ 3,712 and ≥ 3,726 for every pattern. Each such point is a vertex of c' at odd
distance > 7, so ≥ 9, from the hub. ∎

**Computer-checked 3.4 (route numbers).** Two independent enumerations, `routecount.c` (the route search of `twist.c`)
and `routecount2.c` (a separate search over free-group words in the labelling automorphisms), agree. For every pattern
the best pair (hub class X, missed copy c') has α radius-4 twisted centres plus the identity, and:

| q | α | worst pattern | m₂ of its best pair | q⁵ − αq⁴ − m₂q² (far vertices per hub, ≥) |
|---:|---:|---|---:|---:|
| 3 | 3 | a b b | 48 | −432 |
| 4 | 3 | a b b | 48 | −512 |
| 5 | 4 | a a b b | 89 | −1,600 |
| 7 | 5 | a a b b b | 134 | −1,764 |
| 8 | 5 | a a b b b | 134 | **3,712** |
| 9 | 6 | a a a b b b | 197 | **3,726** |
| 11 | 7 | a a a b b b b | 262 | **26,862** |
| 13 | 8 | a a a a b b b b | 347 | **84,162** |

(`routecount2 sweep 3 9` also gives q = 6, 10, 12, 14, 15, 16: −612, 20,300, 65,952, 162,484, 206,550, 348,160. Logs
`logs/routecount.txt`, `logs/routecount2.txt`.)

**Theorem 3.5 (all readings, dualities allowed).** For q ∈ {8, 9, 11, 13}, every reading of Figs. 2.21a/b and every
choice of inner class per block (84 multisets of the block kinds aP, aL, bP, bL at q = 9; 56, 120, 165 at q = 8, 11, 13),
every geometric labelling gives diameter ≥ 9.

*Proof.* Lemma 2.4 and the count of Theorem 3.3, taking one radius-4 centre as the reference t: the other centres meet
opp(t) in ≤ q⁴, q³, q², q, 1 points for radius 4, 3, 2, 1, 0 (Lemma 3.1). `routecount2 q α all` gives a pair with a
positive bound for every pattern; the worst bounds equal those of the table above. For q ≠ 3^e, patterns that need a
duality have no geometric labellings, so they are covered vacuously. ∎

**Corollary 3.6.** For the table cells (11,8) 2,246,940, (12,8) 4,650,100, (14,8) and (15,8) 14,172,480 and (16,8)
36,201,060 (ΩH_q, q = 8, 9, 11, 13), no relabelling of the copies by automorphisms of the hexagon, collineations on points
and lines chosen independently, or dualities, gives diameter 8, under any reading of the figures.

## 4. q ≤ 7

At q ≤ 7 the bound of Theorem 3.3 is negative: the α balls of radius 4 could, in principle, cover q⁵ − (number of
points left for the radius-2 balls). Two refinements and the computations follow.

**Lemma 4.1 (Theorem; overlaps, q odd).** For distinct points y, y′, t of Q(6,q) with t not on the line yy′ of PG(6,q):
|y^⊥ ∩ y′^⊥ ∩ opp(t)| ≥ q³ − q. For three points y, y′, y″ not on one line: |y^⊥ ∩ y′^⊥ ∩ y″^⊥ ∩ Q| ≤ (q+1)².

*Proof.* |⟨y,y′⟩^⊥ ∩ Q| = q³+q²+q+1 (Lemma 3.1's proof). For a plane Π spanned by three singular points, the Gram
matrix has zero diagonal, so its rank is 3, 2 or 0, and Π^⊥ (4-dimensional) has a radical of dimension 0, 1 or 3. Its
quadric points then number (q+1)² or q²+1, q²+q+1, or q²+q+1. So |Π^⊥ ∩ Q| ≤ (q+1)². Apply this with Π = ⟨y,y′,t⟩
and subtract. ∎ (Sampled check: `overlaps.py`; the minimum q³ − q and the maximum (q+1)² occur.)

**Theorem 4.2 (q = 7 in general position).** Let q = 7, reading 2, any pattern and any twisted labelling, and (k, c')
the best pair of Computer-checked 3.4 (five twisted radius-4 centres y_i(t) = λ_{c'}λ_{c_i}⁻¹(t), m₂ ≤ 134). If for some
point t the six points t, y₁(t), …, y₅(t) are distinct and no three of them lie on a line of PG(6,7), then hub (t,k) has
at least 956 vertices of c' at distance ≥ 9.

*Proof.* Bonferroni on the five sets Cᵢ = yᵢ^⊥ ∩ opp(t): |⋃Cᵢ| ≤ 5q⁴ − 10(q³ − q) + 10(q+1)² = 12,005 − 3,360 + 640 =
9,285 (Lemma 4.1). The radius-2 balls add ≤ 134 · 49 = 6,566. And 16,807 − 9,285 − 6,566 = 956. ∎

The hypothesis fails at t only if three of the six points are pairwise perpendicular (hexagon distance ≤ 4) and
collinear in PG(6,7). For a collineation g that is not a long root elation, g(t) ⊥ t holds for about 1/q of the points t
(sampled: 0.14 at q = 7). For the long root elations with a hexagon line as axis it holds for all t, and t, e(t), e′(t)
are collinear for e, e′ in one root group. So a twisted labelling escapes Theorem 4.2 only if its twist differences
behave like elations on every t. We could not exclude that by a proof (see Heuristic 4.4). At q = 5 and q = 4 even the
general-position bound is negative (−1,024 and −357), so the count alone cannot settle them.

**Computer-checked 4.3 (geometric labellings are worse than random ones).** Far pairs (hub, vertex) at distance > 8,
over all 10N hubs. "Random twists": independent random elements of G₂(q) (`mktwist.py rand`). "Annealed": `tanneal.c`
(moves λ_c ← gλ_c or λ_c g, g from a pool of random elements). Singer: λ_c = s^{e_c} for a Singer cycle s of
SL(3,q) ≤ G₂(q). Elation: λ_c in one long root group E_ℓ (order q); elation²: in E_ℓE_m (two lines through a point, order
q²). "General random" is the audit's E[F] for random arbitrary bijections (NOTES.md there), for comparison.

| q | pattern | thesis (all λ = id) | random twists | annealed twists | Singer | elation | elation² | general random (audit) |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 2 | ab | 120,960 | 1,330–1,911 | 805 | | | | ≈ 70 |
| 3 | aba | 7,960,680 | 288,846 | 259,169 | 1,031,433–1,671,280 | 4,133,430 | 2,285,415 | 1,911 |
| 4 | aba | 125,798,400 | 18,464,523 | 18,198,563 | 30,400,167–35,301,378 | 70,522,880 | 40,282,112 | 645,753 |
| 5 | abab | 1,464,750,000 | 209,613,460 | 209,450,727 | 374,719,382 | 744,656,250 | 506,393,750 | ≈ 6.55·10⁶ |
| 7 | aabbb | 4.94·10¹⁰ | 11,180,221,804 | | | | | ≈ 6.5·10⁸ |

The thesis column is 10N · 3α · q⁵ (Theorem 1). Annealing within the class removes 10 % at q = 3, 1.4 % at q = 4 and
0.1 % at q = 5. Logs: `logs/anneal_*.txt`, `logs/structured.txt`, `logs/q7_random_twist_full.txt`.

**Heuristic 4.4 (why geometric labellings fail, and what a better wiring would still need).** In a geometric labelling
a route into a missed copy covers one ball: q⁴ of the q⁵ vertices opposite t. A hub therefore needs at least q one-hop
routes into every missed copy. Gómez's wiring gives some pairs only α ≈ q/2 (Lemma 3.2), which is Theorem 3.3. A
different wiring could give every pair 2α ≈ q + 3 routes, enough by counting. Then a near-exact cover is needed.
Lemma 4.1 says that centres not on a common totally singular line through t overlap in about q³ points each, so the q⁴-sets
can only tile opp(t) when about q of the centres lie on one totally singular line through t. They must lie there for
every t, with fixed group elements. That forces the twist differences g to satisfy g(t) ⊥ t for all t. Over odd q,
b(t, g t) = 0 on all of Q(6,q) should force the form t ↦ b(t, gt) to be a multiple of Q, hence (g ∓ 1)² = 0: a long root
elation (Siegel transformation) x ↦ x + b(x,u)v − b(x,v)u. Sampled check (`logs/siegel_check.txt`): such maps are
collineations of H(q) when ⟨u,v⟩ is a hexagon line and not when it is an ideal line, and random collineations move
about 1/q of the points to perpendicular points. A root group E_ℓ moves t only along the line ⟨t, w_t⟩ (w_t the projection of t on ℓ) and never
reaches w_t itself. That leaves the q⁴ points of opp(t) ∩ w_t^⊥ to the few remaining centres, each covering only about
q³ of them. We believe geometric labellings fail for every wiring and every q ≥ 4, but the steps "near-exact cover ⇒
line structure" and "line structure for all t ⇒ elations of one root group" are not proved here.

## 5. General labellings: what a repair would have to do

For an arbitrary labelling a one-hop route through copy c₁ and class Y reaches
⋃_{a+b ≤ 4} B(T(B(x,a) ∩ cls), b) with T = T_Y(c₁→c'). When T is geometric the three terms a = 0, 2, 4 collapse to one
ball of q⁴ opposite vertices. When T scatters, each term can contribute about q⁴ new vertices, about 3q⁴ per route. That
is why random labellings do so much better than twisted ones in the table above, and why the audit's union bound
(NOTES.md there: ratio ≈ 3 as q grows) cannot exclude a repair. A repair at q ≥ 4 must therefore be "anti-geometric":
every transfer must scatter the radius-2 and radius-4 balls of the hexagon almost perfectly, and the covers of different
hubs must fit together. The audit's first-moment heuristic says random labellings of this kind exist for q ≤ 3 and not
for q ≥ 4 (E[F] is 0.4–1 % of all (hub, missed-copy vertex) pairs at q = 4, 5, 7). Nothing in this note decides the general question.

What the open cells now are, as mathematical questions:
- **(10,8), q = 7.** Does some twisted labelling make every point t degenerate (Theorem 4.2) for every starved pair? If
  not, no geometric labelling repairs ΩH₇. Proving Heuristic 4.4's two steps at q = 7 would settle it.
- **All table cells.** Is there a labelling, necessarily non-geometric, whose transfers tile each missed copy with the
  route sets of §5? A negative answer needs an argument that uses more than counting, since counting allows ≈ 3 covers.

## 6. Files

`research/omega_repair/` (README there): `hexq6.c` (H(q), from claude/own-12-8-cell-ig5jhd), `geo.py` (field,
coordinates, collineation checks, long root elations), `mktwist.py`, `gens.py`, `structured.py` (twist files),
`twist.c` (route formula, explicit graph, BFS, edge list), `tanneal.c` (annealer), `routecount.c`, `routecount2.c`
(route numbers), `counts.c` (Lemma 3.1), `overlaps.py` (Lemma 4.1), `check/` (the audit's omega_eval, unchanged, and
`tolab.py`), `logs/`.
