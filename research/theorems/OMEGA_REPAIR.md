# Repairing Gómez's ΩH_q by relabelling the copies: geometric relabellings cannot work for q ≥ 7

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
2. **Main results (Theorems 3.3, 3.5, 4.5).** Call a labelling *geometric* if every transfer map (the mark of a hub in
   one copy to its mark in another copy) is the restriction of an automorphism of the incidence graph of H(q): a
   collineation, or a duality when q = 3^e. This contains every "collineation coset" labelling, where copy c labels its
   points by a collineation a_c and its lines by a possibly different collineation b_c (the first rung above the thesis).
   **For every q ≥ 7 and every geometric labelling of Gómez's wiring, ΩH_q has diameter ≥ 9.** This holds for any mix
   of the two block types and reading 2 of the figures; for q = 7, 8, 9, 11, 13 it holds for every reading and every
   choice of inner classes, dualities included. **This covers all six table entries (10,8) … (16,8).** In a geometric
   labelling every route from a hub into a copy it misses reaches one ball of the hexagon. Gómez's wiring gives some hub
   only α = ⌊(q+3)/2⌋ routes of length ≤ 7 into some copy ("starved" pairs). For q ≥ 8 a count shows these balls cannot
   cover the copy (Theorem 3.3). For q = 7 the count needs two more ingredients. Bonferroni inequalities settle every
   point t whose six ball centres are in general enough position. The degenerate positions force many perpendicular
   pairs, and a character-sum bound shows that no collineation of H(7) without fixed points moves more than 4,144 of the
   19,608 points to perpendicular points (Lemma 4.4, Theorem 4.5).
3. **Explicit far vertices (q ≥ 8).** In a starved pair, every hub (t, k) has at least q⁵ − αq⁴ − m₂q² vertices at
   distance ≥ 9 in the missed copy: at least 3,712 at q = 8, 3,726 at q = 9, 26,862 at q = 11 and 84,162 at q = 13
   (Computer-checked 3.4). Summed over all starved pairs, every geometric labelling leaves at least 3.3·10⁹ (q = 8),
   7.4·10⁹ (q = 9), 1.6·10¹¹ (q = 11) and 1.4·10¹² (q = 13) far pairs (`logs/total_far_lower_bounds.txt`).
4. **q ≤ 5 (not table values).** Neither the count nor the q = 7 argument is enough (the general-position bound itself
   is negative at q = 4, 5). Computer: geometric labellings are far worse than random arbitrary labellings at every q
   tested. Annealed geometric labellings leave 805 far pairs at q = 2, 259,169 at q = 3, 18.2 million at q = 4 and 209
   million at q = 5, against about 70, 1,911, 646,000 and 6.6 million for random arbitrary labellings. Annealing inside
   the class removes 10 % at q = 3 and under 2 % at q = 4, 5 (Computer-checked 4.6). "Polar" labellings, which keep
   perpendicularity of points but not the hexagon lines, are also worse than random ones (Computer-checked 5.1).
5. **What is left.** A repair at q ≥ 4, if one exists, must use non-geometric labellings whose transfer maps scatter
   balls (§5). No counting argument excludes them (the audit's union bound stays near 3). We found no valid graph, so no
   builder is saved.

Answer to the brief: **(b) is done** for the natural class "π_c in Aut(H(q)) on points and on lines, independently" and
its duality extension, for every q ≥ 7, so for every table cell. (a) found nothing: every structured family tried (Singer
powers, root elation groups, random and annealed twists, polar labellings) is worse than random. (c) is answered inside
the geometric class (item 3: explicit numbers of far vertices per hub and of far pairs), not for general labellings.

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
2), and more generally every geometric labelling in reading 2 or in its point/line dual, ΩH_q has diameter ≥ 9. For the pair (k, c') of
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
distance > 7, so ≥ 9, from the hub. In the dual reading the same pair has its hubs on lines; Lemma 3.1 holds for lines
as well, so the same count applies. ∎

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

## 4. q = 7, and why q ≤ 5 stays open

At q ≤ 7 the bound of Theorem 3.3 is negative: the α balls of radius 4 and the radius-2 balls could, by size alone,
cover opp(t). At q = 7 the overlaps of the radius-4 balls and the group structure of the centres close the gap.

**Setting for this section.** q = 7. Geometric labellings exist only in reading 2 and in its point/line dual (unbarred
hubs on lines, barred hubs on points), because 7 is not a power of 3. A *starved pair* is a hub class X and a copy c'
it misses with exactly five twisted radius-4 centres. Computer-checked 4.0 (`logs/q7_starved_pairs.txt`,
`logs/q7_starved_by_bar.txt`, `routes_dump.c`, the route search of `twist.c`): every block pattern has starved pairs with X
unbarred and starved pairs with X barred, and every starved pair has m₂ ≤ 140. Choose the bar whose hubs sit on the
points of H(7) (unbarred in reading 2, barred in the dual reading). For a hub (t, X) of that class the five radius-4
centres are yᵢ(t) = gᵢ(t), i = 1, …, 5, where the gᵢ = λ_{c'}λ_{cᵢ}⁻¹ (or the analogous products in the dual reading) are
collineations of H(7), so elements of G₂(7) (q is prime). Write Cᵢ = yᵢ^⊥ ∩ opp(t) (Lemma 3.1: |Cᵢ| = q⁴ when yᵢ ≠ t).

**Lemma 4.1 (Theorem; overlaps, q odd).** For distinct points y, y′, t of Q(6,q) with t not on the line yy′ of PG(6,q):
|y^⊥ ∩ y′^⊥ ∩ opp(t)| ≥ q³ − q. For three points y, y′, y″ not on one line: |y^⊥ ∩ y′^⊥ ∩ y″^⊥ ∩ Q| ≤ (q+1)². For
points on one totally singular line ℓ not through t, all pairwise and triple intersections equal ℓ^⊥ ∩ opp(t).

*Proof.* |⟨y,y′⟩^⊥ ∩ Q| = q³+q²+q+1 (Lemma 3.1's proof). For a plane Π spanned by three singular points, the Gram
matrix has zero diagonal, so its rank is 3, 2 or 0, and Π^⊥ (4-dimensional) has a radical of dimension 0, 1 or 3. Its
quadric points then number (q+1)² or q²+1, q²+q+1, or q²+q+1. So |Π^⊥ ∩ Q| ≤ (q+1)². Apply this with Π = ⟨y,y′,t⟩
and subtract. The last sentence holds because y^⊥ ∩ y′^⊥ = ℓ^⊥ ⊆ y″^⊥ for y, y′, y″ ∈ ℓ. ∎ (Sampled check:
`overlaps.py`; the minimum q³ − q and the maximum (q+1)² both occur.)

**Lemma 4.2 (Theorem; coincidences).** If two of t, y₁(t), …, y₅(t) coincide, hub (t, X) has at least
q⁵ − 4q⁴ − m₂q² ≥ 16,807 − 9,604 − 140·49 = 343 vertices of c' at distance ≥ 9.

*Proof.* At most four distinct centres other than t remain; Lemma 3.1 as in Theorem 3.3. ∎

**Lemma 4.3 (Computer-checked; degenerate positions).** Suppose t, y₁, …, y₅ are distinct. Record which yᵢ lie on a
common totally singular line through t ("aligned classes": their sets Cᵢ are disjoint) and which sets of ≥ 3 yᵢ lie on a
line of PG(6,7) not through t ("rich lines"). Bonferroni's inequality |⋃Cᵢ| ≤ S₁ − S₂ + S₃, with the overlaps of
Lemma 4.1 (and the exact value 5q⁴ − 4|ℓ^⊥ ∩ opp(t)| when all five yᵢ lie on one rich line), together with ≤ 140
radius-2 balls of ≤ 49 points, leaves a vertex of c' at distance ≥ 9 from (t, X) for 8 of the 17 possible structure
types. Every one of the other 9 types forces **at least 6** of the 15 pairs among {t, y₁, …, y₅} to lie on a common
totally singular line, hence to be perpendicular (`degen.py`, log `logs/degen_q7.txt`). The general-position type
alone gives ≥ 662 far vertices. As a check, `degen_check.py` built 4,000 configurations in H(7) of 15 of the 17 types
and found the exact union never above the bound (`logs/degen_check_q7.txt`).

**Lemma 4.4 (Theorem; few points are moved to perpendicular points).** Let q be odd with 3 | q − 1, and let h ∈ G₂(q)
fix no point of H(q). Then Perp(h) := {s ∈ P : h(s) ⊥ s} has at most (q⁵−1)/(q−1) + q^{3.5} + q³ + (q−2)q^{1.5}
points: at most 4,144 of the 19,608 points when q = 7.

*Proof.* Let F(v) = b(v, hv). Its polar form is b(v, (h + h⁻¹)w), so for c ∈ F_q the form R_c = F − cQ has rank
7 − d_c with d_c = dim ker(h + h⁻¹ − c). With ψ a nontrivial additive character,
#{v : Q(v) = F(v) = 0} = q⁻² Σ_{a,b} Σ_v ψ(aQ(v) + bF(v)). The terms with b = 0 sum to q⁷, because #{Q = 0} = q⁶. For
b ≠ 0, aQ + bF = b R_{−a/b}, and a Gauss sum gives |Σ_v ψ(bR_c(v))| = q^{7 − (7 − d_c)/2}. Hence
|Perp(h)| ≤ (q⁵−1)/(q−1) + Σ_{c ∈ F_q} q^{1.5 + d_c/2}. The kernels for different c are independent, so Σ d_c ≤ 7.
Each d_c ≤ 4:
(i) if x² − cx + 1 has roots μ ≠ ±1 in F_q, then ker = E_μ ⊕ E_{μ⁻¹}, and a nonzero μ-eigenvector v has
b(v,v) = μ²b(v,v), so it is singular: a fixed point. Hence d_c = 0.
(ii) c = ±2: the (±1)-eigenspace contains no singular vector (it would be a fixed point), so it has dimension ≤ 2 and
ker(h ∓ 1)² has dimension ≤ 4.
(iii) x² − cx + 1 irreducible with roots μ, μ⁻¹ = μ^q: d_c = 2·dim ker(h − μ), at most twice the multiplicity of μ.
The eigenvalues of an element of G₂ on its 7-dimensional module are 1, x, y, xy, x⁻¹, y⁻¹, (xy)⁻¹, and μ can occur three
times only if μ³ = 1. When 3 | q − 1 that puts μ in F_q, a contradiction. So d_c ≤ 4.
The sum Σ q^{d_c/2} is convex in each d_c, so it is largest for one d_c = 4, one d_c = 3 and the rest 0. ∎ (Sampled:
229 fixed-point-free elements of G₂(7), `perpbound.py`: max d_c = 4, max Σd_c = 7, bound − |Perp| ≥ 111; the true values
are 2,752 and 2,850, `logs/fpfperp_q7.txt`.)

**Theorem 4.5.** For q = 7, every block pattern and every geometric labelling (reading 2 or its dual), ΩH₇ has
diameter ≥ 9.

*Proof.* Suppose the diameter is 8 and take a starved pair (X, c') whose hubs sit on points (Computer-checked 4.0).
Consider the 15 collineations gᵢ (1 ≤ i ≤ 5) and gᵢ⁻¹g_j (i < j). Two of t, y₁(t), …, y₅(t) coincide exactly when t
is fixed by one of them. By Lemma 4.2 none of the 15 has a fixed point. Then for every point t the six points are
distinct, and by Lemma 4.3 at least six of the 15 pairs are perpendicular. Pair (t, yᵢ) is perpendicular iff
t ∈ Perp(gᵢ), and pair (yᵢ, y_j) iff t ∈ Perp(gᵢ⁻¹g_j), since collineations preserve perpendicularity. Summing over t,
Σ |Perp(h)| ≥ 6N = 117,648 over the 15 elements h, while Lemma 4.4 gives Σ |Perp(h)| ≤ 15 · 4,144 = 62,160. This is
a contradiction. ∎

**Corollary 4.7 (all table cells).** For every table value of Gómez's ΩH_q, (10,8) 1,176,480, (11,8) 2,246,940, (12,8)
4,650,100, (14,8) and (15,8) 14,172,480, (16,8) 36,201,060 (q = 7, 8, 9, 11, 11, 13), no relabelling of the copies by
automorphisms of the hexagon gives diameter 8. This covers collineations chosen independently on points and lines, and
dualities, under any reading of Figs. 2.21a/b and any mix of block types (Theorems 3.3, 3.5, 4.5).

**Why q = 4, 5 stay open in this class.** The general-position Bonferroni bound is already negative (−357 at q = 4,
−1,024 at q = 5): the radius-2 balls are too many relative to opp(t). At q = 5, moreover, 3 ∤ q − 1, so Lemma 4.4's
step (iii) fails. These q are not table values. Computationally the class is hopeless there (next item).

**Computer-checked 4.6 (geometric labellings are worse than random ones).** Far pairs (hub, vertex) at distance > 8,
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
0.1 % at q = 5. Logs: `logs/anneal_*.txt`, `logs/structured.txt`, `logs/q7_random_twist_full.txt`. For the random q = 7
twists, 19,580 of the 19,608 points t are in general position for a starved pair (`genpos.py`, `logs/genpos_q7.txt`).

**Heuristic 4.8 (other wirings).** Theorems 3.3 and 4.5 use Gómez's wiring through the starved pairs, where only
α ≈ q/2 of a hub's 2α copies reach the missed copy in one pass. A different wiring could give every pair about q + 3
one-hop routes, which is enough by size. A near-exact cover is then needed, and Lemma 4.1 says that centres not on a
common totally singular line through t overlap in about q³ points. So about q of the centres must lie on one line
through t, for every t, with fixed group elements. That needs twist differences with g(t) ⊥ t for all t: over odd q
these should be exactly the long root elations x ↦ x + b(x,u)v − b(x,v)u with ⟨u,v⟩ a hexagon line (sampled check,
`logs/siegel_check.txt`: such maps are collineations for hexagon-line axes, not for ideal axes). A root group moves t
only along ⟨t, w_t⟩ (w_t the projection of t on the axis) and never reaches w_t. That leaves q⁴ opposite points to the
few other centres. Moreover elations have fixed points, which Lemma 4.2's argument penalises. We believe geometric
labellings fail for every wiring once q ≥ 7, but this is not proved.

## 5. General labellings: what a repair would have to do

For an arbitrary labelling a one-hop route through copy c₁ and class Y reaches
⋃_{a+b ≤ 4} B(T(B(x,a) ∩ cls), b) with T = T_Y(c₁→c'). When T is geometric the three terms a = 0, 2, 4 collapse to one
ball of q⁴ opposite vertices. When T scatters, each term can contribute about q⁴ new vertices, about 3q⁴ per route. That
is why random labellings do so much better than twisted ones in the table above, and why the audit's union bound
(NOTES.md there: ratio ≈ 3 as q grows) cannot exclude a repair. A repair at q ≥ 4 must therefore be "anti-geometric":
every transfer must scatter the radius-2 and radius-4 balls of the hexagon almost perfectly, and the covers of different
hubs must fit together. The audit's first-moment heuristic says random labellings of this kind exist for q ≤ 3 and not
for q ≥ 4 (E[F] is 0.4–1 % of all (hub, missed-copy vertex) pairs at q = 4, 5, 7). Nothing in this note decides the general question.

**Computer-checked 5.1 (polar labellings).** Point labellings by isometries of the quadric Q(6,q) (random products of
Siegel transformations with arbitrary totally singular axes) keep perpendicularity (hexagon distance ≤ 4 between points)
but not the hexagon lines. With `check/omega_eval` (reading 2, aba): at q = 4, polar points with random lines leave
1,941,274 far pairs and polar points with untwisted lines 10,331,778, against 642,969 for random points and random lines;
at q = 3 the numbers are 9,750 and 113,644 against 1,944. The more of the hexagon's structure a labelling keeps, the
worse it does (`polar.py`, `logs/polar_classes.txt`; the run with one collineation on both sides reproduces the thesis
counts, as Lemma 1.2 says).

What the open cells now are, as mathematical questions:
- **All table cells, non-geometric labellings.** Is there a labelling of Gómez's wiring, necessarily non-geometric
  (Corollary 4.7), whose transfers tile each missed copy with the route sets above? A negative answer needs more than
  counting, since counting allows about 3 covers.
- **Other wirings with geometric labellings** (Heuristic 4.8): the two steps "near-exact cover ⇒ line structure" and
  "line structure for all t ⇒ elations of one root group".
- **q = 4, 5 in the geometric class** (not table values): the counts above are not enough.

## 6. Files

`research/omega_repair/` (README there): `hexq6.c` (H(q), from claude/own-12-8-cell-ig5jhd), `geo.py` (field,
coordinates, collineation checks, long root elations), `mktwist.py`, `gens.py`, `structured.py` (twist files),
`twist.c` (route formula, explicit graph, BFS, edge list), `tanneal.c` (annealer), `routecount.c`, `routecount2.c`
(route numbers, totals), `counts.c` (Lemma 3.1), `overlaps.py` (Lemma 4.1), `degen.py`, `degen_check.py` (Lemma 4.3),
`perpbound.py`, `fpfperp.py` (Lemma 4.4), `genpos.py`, `polar.py` (Computer-checked 5.1), `check/` (the audit's
omega_eval, unchanged, and `tolab.py`), `logs/`.
