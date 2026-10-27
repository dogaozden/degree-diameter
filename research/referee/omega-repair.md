# Referee report: geometric relabellings of Gómez's ΩH_q (job referee-omega-repair, 2026-10-27)

Opus referee session, branch `claude/referee-omega-repair-qt17fb`. Tools and logs: `research/referee/omega-repair/`.

Under review: `research/theorems/OMEGA_REPAIR.md` on branch `claude/thm-omega-repair-m4luls` (commit 5f64a1d), with its
tools and logs in `research/omega_repair/`. Background: Gómez's thesis §2.9.3; `research/squads/cells/d12D8_table.md`
(branch `claude/own-12-8-cell-ig5jhd`); its referee report `research/referee/omega-dq.md` (branch
`claude/omega-dq-referee-bzzlid`).

I checked every lemma and theorem by hand and recomputed the numbers with my own code. My code includes a new hexagon
builder (split octonions, not the note's `hexq6.c`), new collineations, a new route enumerator, a new ΩH_q builder and
BFS, and a new enumeration of the q = 7 configurations. I used none of the note's code, with one exception: §5.4 runs its
saved q = 3 twist file on the hexagon it was written for.

## Verdict

| claim (note's numbering) | verdict |
|---|---|
| Definition of *geometric* and *twisted* labellings (§1.2) | **Precise, inside the note's model**: each copy c carries one point labelling P_c and one line labelling L_c, shared by both hub classes of a bar that meet c. The note should say so in its main statement (see "What cannot be claimed"). |
| Lemma 1.1 (normal form) | **Correct.** |
| Lemma 1.2 (one collineation per copy gives the thesis graph) | **Correct.** The duality case is simpler than stated: applying δ_c⁻¹ to the copy gives a graph isomorphic to the thesis graph itself, so Theorem 1 of d12D8_table.md applies for every q (no need for Theorem 2 or q ≥ 7). Checked by BFS at q = 7 (§5.3). |
| Lemma 2.1 (routes reach balls) | **Correct.** Checked by hand. My own walk enumeration, which does not use the lemma's families, gives exactly the union of balls the BFS reaches, on the explicit graph at q = 7, 8 and 9 (14 instances, §5.3). |
| Computer-checked 2.2 | **Spot-checked**: q = 3, the note's annealed twist file. Far pairs from hubs 259,169; from all vertices 518,338, exactly twice (§5.4). |
| Lemma 2.3 (only hub–missed-copy pairs matter) | **Correct.** One index slip in (ii): in a b-block, P-hub k and L-hub j̄ share a copy unless k − j = 4, not 3. The conclusion is unaffected. The lemma is not used by the lower bounds. |
| Lemma 2.4 (geometric labellings, any reading) | **Correct**, but it is not needed: see Theorem 3.5. |
| Lemma 3.1 (constants) | **Correct, for points and lines and every radius.** The odd radii are only computer-checked in the note (q ≤ 7) but are used at q = 8–27. They follow for every q because the incidence graph of a generalized hexagon of order (q,q) is distance-regular. I computed all values from its intersection array (§3). |
| Lemma 3.2 (starved pair) | **Correct** (checked by hand). |
| **Theorem 3.3** (q ≥ 8, reading 2 and its dual) | **Correct.** The analytic bound for q ≥ 10 checks. At q = 8, 9 the exact route numbers are reproduced by my enumerator. |
| Computer-checked 3.4 (table) | **Reproduced exactly** for q = 7, 8, 9, 11, 13: the worst pattern, m₂ of its best pair, and the bound (3,712, 3,726, 26,862, 84,162). |
| Theorem 3.5 (all readings, dualities) | **Correct, but implied by Theorem 3.3.** For q = 3^e, applying a duality to every copy whose unbarred hubs sit on lines turns any reading, with a geometric labelling, into reading 2 with a geometric labelling (same block pattern). For q ≠ 3^e only reading 2 and its dual have geometric labellings. So the conclusion holds for **every** q ≥ 7, every reading and every inner class (per block or per copy), not just the listed q. The 816-pattern run at q = 27 is a consistency check, not a needed step. |
| Corollaries 3.6, 4.6 | **Correct**, with the scope wording below. |
| Lemma 4.1 (overlaps, q odd) | **Correct** (proof checked; extreme values 336 = q³ − q and 64 = (q+1)² attained in my sampling). |
| Lemma 4.2 (coincidences) | **Correct** (16,807 − 9,604 − 6,860 = 343). |
| Lemma 4.3 (degenerate positions) | **Correct.** My own enumeration gives the same 353 labelled configurations, 17 types, 9 types without a forced far vertex, and at least 6 forced perpendicular pairs in each of those 9. No Bonferroni bound was violated in 2,500 explicit configurations in Q(6,7) (14 types realised). |
| **Lemma 4.4** (character-sum bound) | **Correct.** Every step checks (§4.3). Sampling: \|Perp(h)\| ∈ {2,752, 2,850} for 224 fixed-point-free elements, under the bound 4,144. |
| **Theorem 4.5** (q = 7) | **Correct.** |
| Verdict item 3 (far vertices and far pairs, q ≥ 8) | **Reproduced**: per-hub bounds at q = 8, 9, 11, 13; totals 3.33·10⁹ (q = 8) and 7.43·10⁹ (q = 9). I did not recompute the totals at q = 11, 13. |
| Computer-checked 4.7 (q ≤ 7 tables) | **One number re-checked** (q = 3 annealed, 259,169), plus the thesis column (10N·3α·q⁵) by arithmetic. The rest was not re-run. These are measurements, not proofs. |
| Computer-checked 5.1 (polar labellings) | Not re-checked. |
| Heuristic 4.8, §5 | Heuristics, labelled as such. No verdict. |

**What can be claimed** (my recommended wording):

> Give each copy of the hexagon in Gómez's ΩH_q its own labelling: a bijection from the rows to the points and one to
> the lines, used by every hub class of that colour that meets the copy. Call the labelling geometric if every transfer
> map between two copies met by one hub class is induced by an automorphism of the incidence graph of H(q) (a
> collineation, or a duality when q = 3^e). For every q ≥ 7, every geometric labelling gives diameter ≥ 9. This holds
> in every reading of Figs. 2.21a/b, for every choice of inner classes and every mix of block types. It covers all six
> table entries (10,8) 1,176,480, (11,8) 2,246,940, (12,8) 4,650,100, (14,8) and (15,8) 14,172,480, and (16,8)
> 36,201,060. For q ≥ 8 the proof is a ball-counting argument. It gives explicit numbers: some hub class X and missed
> copy c′ have at least q⁵ − αq⁴ − m₂q² vertices of c′ at distance ≥ 9 from every hub of X (3,712, 3,726, 26,862 and
> 84,162 at q = 8, 9, 11, 13). For q = 7 the proof adds Bonferroni inequalities and a character-sum bound on how many
> points a fixed-point-free element of G₂(7) moves to perpendicular points.

**What cannot be claimed:**
- Anything about **non-geometric labellings** (arbitrary bijections per copy). These stay open for every q ≥ 4, and at
  q = 2, 3 they do give diameter 8. The note says this itself.
- Anything about labellings chosen **per (hub class, copy)**, where the two hub classes of one bar meeting a copy may
  use different bijections. These are outside the note's model, even when every transfer is a collineation. The
  counting method fails there for every q: every copy met by X shares a class with c′, so there are at least
  2α ≥ q + 2 distinct radius-4 centres (q = 8: 10 centres and 318 radius-2 centres, bound −24,448; q = 13: 16 and 864,
  bound −203,138; `logs/perclass.txt`). Whether such a labelling can give diameter 8 is open.
- Anything about **other wirings** of the hubs (Heuristic 4.8 is a heuristic).
- **q ≤ 5 in the geometric class.** There is no proof, only measurements on random and annealed instances. The general
  bound is negative there (−357 at q = 4, −1,024 at q = 5), and Lemma 4.4's step (iii) needs 3 | q − 1, which fails at
  q = 5. These q are not table values. The subclass a_c = b_c is settled for every q in reading 2 (Lemma 1.2 and
  Theorem 1 of d12D8_table.md).
- That no (Δ, 8) graph of these orders exists. The cells remain "no checkable graph of diameter 8".

## 1. Definitions (§1)

**The model.** A labelling gives each copy c bijections P_c: [N] → P and L_c: [N] → L. Hub (t, k) is joined to P_c(t)
in each copy c it meets (reading 2), and hub (m, k̄) to L_c(m). The transfer of class Y from c to d is P_d P_c⁻¹ (or
L_d L_c⁻¹, or a mixed form in the other readings). It is defined only when Y meets both c and d. *Geometric*: every
transfer is induced by an element of Aut(I). Since a collineation is determined by its action on points, "restriction"
is unambiguous. The definition is precise.

**Geometric = twisted, up to isomorphism, in reading 2.** The note uses this but only sketches it (proof of Lemma 2.4).
Here is the argument. Inside a block, the five classes of one bar link the five positions in a 5-cycle, and each class
meets two copies in every block. So the graph on copies "c ~ d if an unbarred class meets both" is connected, and so is
the barred one. If every transfer is a collineation, then P_c P_{c₀}⁻¹ is a collineation a_c for every c, so
P_c = a_c P′ with P′ = P_{c₀}. Similarly L_c = b_c L′. Unbarred and barred rows are separate vertices, so renaming the
unbarred rows by P′⁻¹P₀ and the barred rows by L′⁻¹L₀ gives an isomorphic graph with P′ = P₀ and L′ = L₀. That is a
twisted labelling.

**Scope.** The model makes both unbarred classes meeting copy c use the same P_c. Labellings per (class, copy), with
hub (t, Y) on μ_{Y,c}(t), are more general. Renaming rows per class cannot reduce them to per-copy labellings, because
μ_{Y,c}⁻¹μ_{Y′,c} may vary with c. With every μ a collineation, they meet the wording "every transfer is induced by an
automorphism" but are not in the model. The note's main statement ("every geometric labelling of Gómez's wiring")
should name the per-copy model, as in my suggested wording above.

**Lemma 1.1.** Applying a_c⁻¹ to copy c is an automorphism of the copy and preserves the hub edges. The result is
P_c = P₀ and L_c = a_c⁻¹b_cL₀. Renaming rows completes the proof. Correct.

**Lemma 1.2.** With a_c = b_c, λ_c = id, and the graph is the thesis graph. Correct, and checked: with a_c = b_c random
at q = 7, the distance profile from a hub is identical to the thesis profile (1, 10, 84, 615, 4,320, 30,240, 211,680,
305,270, 372,155, 252,105), from a P-hub and from an L-hub (`logs/bfs_q7.txt`). Duality case: a duality is an
automorphism of the graph I. Applying δ_c⁻¹ to all of copy c therefore maps the relabelled graph onto the thesis graph,
edge for edge. The note says "a change of inner and outer class in copy c, the setting of Theorem 2 there". That is
true but weaker than necessary: the graph is isomorphic to the thesis graph, so Theorem 1 of d12D8_table.md gives
diameter ≥ 9 in reading 2 for every q.

## 2. Routes (§2)

**Lemma 2.1.** I checked the case analysis line by line:
- A path from the hub to a point of c′ of length ≤ 7 visits r ≤ 4 copies, with Σaᵢ ≤ 8 − 2r.
- Passes through P-hubs keep the point. Passes through L-hubs apply λ_dλ_c⁻¹. Collineations commute with balls.
- The parities force the listed shapes. The two-L-pass case with a₂ = 0 must use the same row m twice, so it telescopes
  to λ_{c′}λ_{c₁}⁻¹.

Correct. As an independent check, `myroutes.py` enumerates all walks symbolically. It allows any pass through any class
at a vertex of the right colour, tracks the reduced free-group word, and does not use the lemma's families. Its
starved-pair data at q = 7 equal the note's `logs/q7_starved_by_bar.txt` exactly:

| pattern | starved pairs, X unbarred (m₂) | starved pairs, X barred (m₂) |
|---|---|---|
| aaaaa, bbbbb | 50 (104) | 50 (104) |
| aaaab | 20 (122) | 5 (140) |
| aaabb | 15 (134) | 10 (140) |
| aabbb | 10 (140) | 15 (134) |
| abbbb | 5 (140) | 20 (122) |

No route ever gives a radius-0 centre other than the identity. Every pair (X, c′) has at least α twisted radius-4
centres (`logs/routes_q7_starved.txt`). On explicit graphs (§5.3), the union of the predicted balls equals the set the
BFS reaches, in all 14 instances.

**Lemma 2.3.** I checked (i) for all position differences and both block types, (ii) and (iii). In (ii), for a
b-block, P-hub k and L-hub j̄ share a copy iff k − j ∈ {0, 1, 2, 3}. The note says "unless k − j = 3"; it should be 4.
Since the a-blocks cover every j ≠ k and the b-blocks cover j = k, the conclusion stands. Point–point pairs in
different copies are not spelled out in (i), but they work the same way (≤ 2 + 6 or 1 + 2 + 5 = 8). The lemma is only
needed for the "⟺" remark after it, not for any lower bound.

**Lemma 2.4 / Theorem 3.5: a simplification.** For q = 3^e, take any reading (inner classes chosen per block, or even
per copy) and any geometric labelling. Apply a duality δ to every copy in which the unbarred hubs sit on lines. This is
an isomorphism of graphs, and the new transfers are old transfers composed with δ or δ⁻¹, so they are still in Aut(I).
The result is reading 2 with a geometric labelling, on the same a/b pattern. For q ≠ 3^e, transfers from points to
lines would need a duality. So every class must keep one colour in all its copies, which forces reading 2 or its dual,
even if inner classes are chosen per copy. Hence Theorem 3.3 alone covers every reading for every q ≥ 8, and with
Theorem 4.5, for every q ≥ 7. The note's observation that "the worst bounds equal those of the table above" at
q = 9, 13, 27 is what this predicts.

## 3. The counting theorem (§3)

**Lemma 3.1.** Because s = t = q, the incidence graph of a generalized hexagon of order (q,q) is distance-regular, with
intersection array {q+1, q, q, q, q, q; 1, 1, 1, 1, 1, q+1}. So |B(z,R) ∩ opp(t)| = Σ_{i≤R} p^d_{i,6} depends only on
d = d(t,z) and q, for points and lines alike. `drg.py` computes the p^d_{ij} from the array (`logs/lemma31_drg.txt`):

| R | d(t,z) = 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| 4 (z same type) | 0 | | q⁴ | | q⁴ | | q⁴ |
| 3 (z other type) | | 0 | | q³ | | q³ | |
| 2 | 0 | | 0 | | q² | | q² |
| 1 | | 0 | | 0 | | q | |
| 0 | 0 | | 0 | | 0 | | 1 |

These are the note's values, for every q. The note's hand proof for points (via Q(6,q)) is also right. For the odd
radii, which Theorem 3.5 uses at q = 8–27, the note relies on Computer-checked 3.1′ at q ≤ 7. Distance-regularity
closes that gap. (With §2's simplification, Theorem 3.5 is not needed anyway.)

**Lemma 3.2.** I checked by hand: c′ at position k+3 of an a-block, or at position k in the all-b case. Exactly one copy
per block of C(k) shares a barred class with c′. In the same way, barred starved pairs exist in every pattern: c′ at
position k+3 of a b-block, or k+1 of an a-block if all blocks are a. This matches the enumeration.

**Theorem 3.3.**
- The covering families give m₂ ≤ (4α − 1) + 2α·2(2α − 1) = 8α² − 1. Correct.
- With α ≤ (q+3)/2, the condition q²(q − α) ≥ 8α² follows from q³ − 7q² − 24q − 36 ≥ 0. That holds at q = 10 (value 24)
  and the function increases from there. Correct.
- For q = 8, 9 the exact m₂ is needed. My sweep over all block patterns (`sweep.py`, any order of blocks is equivalent
  by block swaps) gives:

| q | α | worst pattern | m₂ of its best pair | bound | note |
|---:|---:|---|---:|---:|---:|
| 7 | 5 | aabbb / aaabb | 134 | −1,764 | −1,764 |
| 8 | 5 | aabbb / aaabb | 134 | **3,712** | 3,712 |
| 9 | 6 | aaabbb | 197 | **3,726** | 3,726 |
| 11 | 7 | aaabbbb / aaaabbb | 262 | **26,862** | 26,862 |
| 13 | 8 | aaaabbbb | 347 | **84,162** | 84,162 |

Logs: `logs/sweep_q8.txt`, `sweep_q9.txt`, `sweep_q11.txt`, `sweep_q13.txt`. Every best pair has exactly α twisted
radius-4 centres and no radius-0 centre other than the identity. (The identity ball lies in B(t, 4), so it misses
opp(t) whatever its radius.)

**Total far pairs** (verdict item 3). Summing N·max(0, bound) over all pairs (X, c′), the minimum over patterns is
3.331·10⁹ at q = 8 (25 positive pairs in aabbb) and 7.426·10⁹ at q = 9 (30 in aaabbb), as in the note
(`logs/total_far_bounds_q8_q9.txt`). Different pairs (X, c′) give disjoint sets of (hub, vertex) pairs, so the sum is a
valid lower bound.

## 4. q = 7 (§4)

### 4.1 Lemmas 4.1–4.2

**Lemma 4.1.**
- The Gram matrix of three singular points has zero diagonal and determinant 2abc. Its rank is 3, 2 or 0, never 1.
- rad(Π^⊥) = Π ∩ Π^⊥ = rad(Π), so it has dimension 0, 1 or 3. The quadric points of Π^⊥ number (q+1)² or q² + 1, then
  q² + q + 1, then q² + q + 1. In the last case Π^⊥ = Π ⊕ ⟨w⟩ with Q(w) ≠ 0, because Q(6,q) has no totally singular
  subspace of vector dimension 4.
- The hypothesis "t not on the line yy′" is exactly "y, y′ not aligned with t". A non-perpendicular pair spans a
  hyperbolic line with only two singular points.

Correct. Sampling on my H(7): pair overlaps in opp(t) take the values {336, 343, 350}, triple overlaps {50, 57, 64}.
Both bounds are attained (`logs/lemma41_43_configs_q7.txt`).

**Lemma 4.2.** Correct.

### 4.2 Lemma 4.3

The rules used:
- aligned pair → overlap 0;
- any other pair → ≥ q³ − q;
- triple with an aligned pair → 0;
- triple on a rich line ℓ → X_ℓ;
- any other triple → ≤ (q+1)².

A rich line with m points contributes −(C(m,2) − C(m,3))X_ℓ to S₂ − S₃. That is −2X_ℓ for m = 3, 4, so bounding
X_ℓ ≥ q³ − q is legitimate. For m = 5 the exact union 5q⁴ − 4X_ℓ is used. Three collinear singular points span a
totally singular line, so every collinear triple is an aligned triple or lies on a rich line. Over-counting types is
safe, since a geometrically impossible type only adds cases.

`mytypes.py` enumerates the partitions of {y₁..y₅} into aligned classes, and the systems of rich lines (each meets each
class at most once; two share at most one point). Result: 353 labelled configurations, 17 types, the same 17 far-vertex
bounds (662 down to −2,058), 9 types with bound ≤ 0, and minimum forced perpendicular pairs 6 among those 9, attained
by five singletons with one rich 4-line (`logs/lemma43_types.txt`). This matches `logs/degen_q7.txt` line for line.

`e2e43.py` builds 2,500 configurations in Q(6,7), biased towards degeneracy (points of a totally singular plane through
t, of a totally singular line not through t, or random). It classifies each one and compares the exact
|⋃ yᵢ^⊥ ∩ opp(t)| with its type's bound. There were no violations; 14 of the 17 types were realised. The smallest
margin was 28, in type (1,4).

### 4.3 Lemma 4.4

- **Lift.** For q = 7, Aut H(7) = G₂(7) (q is prime, so there are no field automorphisms). A collineation is induced by
  a unique matrix of determinant 1, because λ⁷ = λ on F₇. That matrix lies in G₂(7) ≤ SO(7,7). The note's remark that
  "−h gives the same Perp" is true but beside the point: −h has determinant −1.
- **Character sum.** The b = 0 terms give q·q⁶ = q⁷. For b ≠ 0 the substitution c = −a/b runs over F_q for each b. A
  rank-r quadratic form on F_q⁷ has |Σψ| = q^{7−r/2}. So |#{Q = F = 0} − q⁵| ≤ (q−1)Σ_c q^{1.5+d_c/2}, and dividing
  (# − 1) by (q − 1) gives the stated bound on |Perp|.
- **Rank.** The polar form of F − cQ is b(v, (h + h⁻¹ − c)w), because h is an isometry. b is nondegenerate in odd
  characteristic, so the rank is 7 − d_c.
- **Σd_c ≤ 7.** For c ≠ c′, x² − cx + 1 and x² − c′x + 1 are coprime (their difference is a multiple of x), so the
  kernels are independent.
- **d_c ≤ 4.**
  - (i) The factors are coprime, so the kernel is a sum of true eigenspaces. An eigenvector of eigenvalue μ ≠ ±1 is
    singular, so it gives a fixed point (every point of Q(6,q) is a point of H(q)).
  - (ii) An anisotropic eigenspace has dimension ≤ 2 (Chevalley–Warning), and dim ker N² ≤ 2·dim ker N.
  - (iii) The eigenvalues are 1, x₁^{±1}, x₂^{±1}, x₃^{±1} with x₁x₂x₃ = 1. A triple occurrence of μ ≠ ±1 needs three
    different indices, so μ^{±1±1±1} = 1, which forces μ³ = 1, and that puts μ in F_q when 3 | q − 1. The multiplicity
    argument uses the characteristic polynomial, so it covers non-semisimple h.
- **Extremal case.** (4, 3, 0, …, 0) weakly majorises every feasible vector, and Σq^{d/2} is increasing and convex.
- **Arithmetic.** At q = 7: 2,801 + 907.49 + 343 + 92.60 = 4,144.09.

Correct. `myperp44.py` samples 400 products of my generators, of which 224 are fixed-point-free on points. It gives max
d_c = 2, max Σd_c = 7, |Perp(h)| ∈ {2,752, 2,850}, and smallest gap between the per-element bound and |Perp| of 111.1.
On 30 sources it also checks that b(s, s′) = 0 ⟺ d_I(s, s′) ≤ 4, with no mismatch among 30 × 19,608 pairs
(`logs/lemma44_sampling_q7.txt`). These values agree with the note's `logs/fpfperp_q7.txt` (2,752 and 2,850).

### 4.4 Theorem 4.5

Diameter 8 means every hub of the starved class reaches every point of c′ within 7 steps.
- If one of the 15 elements gᵢ, gᵢ⁻¹g_j has a fixed point t₀ (including gᵢ = g_j), then hub (t₀, X) has a coincidence,
  and Lemma 4.2 gives a far vertex.
- Otherwise every t is in one of the 9 types, and has ≥ 6 perpendicular pairs among the 15. gᵢ(t) ⊥ g_j(t) iff
  t ∈ Perp(gᵢ⁻¹g_j), because collineations preserve ⊥. So Σ_h |Perp(h)| ≥ 6·19,608 = 117,648 > 15·4,144 = 62,160.

The starved pair must have its hubs on points. Every pattern has starved pairs of both bars (§2), so this works in
reading 2 (unbarred class) and in its dual (barred class). Correct.

On an explicit ΩH₇ (aabbb, random twisted labelling, barred hub on lines in reading 2), the hub has eccentricity 9 and
5,221 lines of the missed copy at distance ≥ 9 (`logs/bfs_q7.txt`). This is consistent with the theorem; it is not a
test of it.

## 5. My own computations

### 5.1 Hexagons

`buildhex.py` builds H(q) from split octonions. These are Zorn vector matrices
(a, u, v, b)(a′, u′, v′, b′) = (aa′ + u·v′, au′ + b′u − v×v′, a′v + bv′ + u×u′, bb′ + v·u′), with N = ab − u·v. On
random samples, `octo.py` checks N(xy) = N(x)N(y) and x(xy) = (xx)y over GF(3), GF(4), GF(5), GF(7), GF(8) and GF(9).

- Points are the ⟨x⟩ with tr x = 0 and N(x) = 0.
- The lines through x are the 2-spaces through x inside the 3-dimensional kernel of y ↦ xy.
- Every point has q + 1 lines, and every line has q + 1 points.

`ghcheck.c` runs a 64-source bit-parallel BFS from every vertex. For q = 3, 7, 8, 9, every vertex has sphere sizes
1, q+1, (q+1)q, …, (q+1)q⁴, q⁵, so each incidence graph has girth 12 and diameter 6: a generalized hexagon of order
(q,q) (`logs/ghcheck.txt`).

### 5.2 Collineations

`collin.py` builds two kinds of maps:
- SL(3,q) maps (a, u, v) ↦ (a, Au, A^{−T}v), which are octonion automorphisms;
- Siegel maps x ↦ x + B(x,u)v − B(x,v)u along hexagon lines ⟨u,v⟩.

Every element used (all products of 6–8 generators) is checked to send every line to a line before use
(`logs/collineation_generators.txt`). The hexagon builder, the generators and the line check share no code with the
note's `hexq6.c` or `geo.py`.

### 5.3 BFS on explicit ΩH_q at the thesis orders

`omg.c` builds ΩH_q from the definition, without the normal form. Hub (t, k) goes to point a_c(t) and hub (m, k̄) to
line b_c(m) of copy c, with a_c, b_c independent random collineations. The program checks degrees, simple edges and
bipartiteness, runs a BFS from one hub, and counts the far vertices. `driver.py` evaluates the route words of
`myroutes.py` on the actual collineations (μ_c = a_c⁻¹b_c for an unbarred source, b_c⁻¹a_c for a barred source). It
compares the union of the predicted balls with the BFS reach.

| q | graph | source (starved pair) | far in c′ (BFS) | proved lower bound | predicted = reached | eccentricity |
|---:|---|---|---:|---:|---|---:|
| 7 | ΩH₇ aabbb, 1,176,480 v., 5,882,400 e., 10-regular | (0, 4̄) → copy 22 | 5,221 | > 0 (Thm 4.5) | yes | 9 |
| 8 | ΩH₈ aabbb, 2,246,940 v., 12,170,925 e., degrees 10–11 | (0, 0̄) → copy 13 | 12,943 | 3,712 | yes | 9 |
| 8 | same, other labelling | (5, 0̄) → copy 13 | 12,887 | 3,712 | yes | 9 |
| 8 | ΩH₈ aaabb | (11, 0) → copy 3 | 12,904 | 3,712 | yes | 9 |
| 9 | ΩH₉ aaabbb, 4,650,100 v., 27,900,600 e., 12-regular | (0, 0) → copy 3 | 22,158 | 3,726 | yes | 9 |
| 9 | same, other labelling | (17, 0) → copy 3 | 22,225 | 3,726 | yes | 9 |
| 9 | ΩH₉ aabbbb | (4, 0̄) → copy 13 | 22,596 | 4,536 | yes | 9 |

Controls, with the thesis labelling:
- q⁵ far vertices in the missed copy (16,807; 32,768; 59,049).
- At q = 9, the distance profile 1, 12, 124, 1,148, 10,350, 93,150, 838,350, 1,167,858, 1,476,225, 1,062,882 is the
  one in d12D8_table.md §3 and omega-dq.md §3.3.
- Pattern bbbbb gives eccentricity 10, as known.
- A non-starved pair (q = 8, (7, 0) → copy 13) is covered completely, and again predicted = reached.

Logs: `logs/bfs_q7.txt`, `logs/bfs_q8.txt`, `logs/bfs_q9.txt`. The true far counts are 3–6 times the lower bounds, as
expected: the bounds ignore the overlaps of the radius-4 balls.

### 5.4 The note's annealed q = 3 labelling

I built the note's H(3) with its unchanged `hexq6.c` and checked it with my `ghcheck`. All 15 λ_c in
`twists/q3_aba_annealed.bin` are collineations of it (my check). I wired ΩH₃ with my `omg_all.c`. BFS from all 3,640
hubs gives **259,169** pairs at distance > 8, the note's annealed value. BFS from all 14,560 vertices gives 518,338:
each far pair counted once from each end, so every far pair is a (hub, missed-copy vertex) pair. The diameter is 9
(`logs/their_annealed_q3.txt`).

## 6. Smaller points for the note

1. Verdict item 2, Theorem 3.3 and Corollaries 3.6/4.6: state the per-copy model ("one point labelling and one line
   labelling per copy, shared by the hub classes of each bar that meet it"). Also list per-(class, copy) labellings as
   open. The counting method fails there (§1).
2. Theorem 3.5 can be replaced by the duality reduction of §2. The restriction "for q = 7, 8, 9, 11, 13 and 27" in
   verdict item 2 can then be dropped: every reading is covered for every q ≥ 7.
3. Lemma 1.2, duality case: the graph is isomorphic to the thesis graph, so Theorem 1 applies for every q.
4. Lemma 2.3 (ii): "unless k − j = 3" should be "unless k − j = 4".
5. Lemma 3.1: replace "the odd radii are taken from Computer-checked 3.1′" by the distance-regularity argument of §3.
6. Lemma 4.4: say that the determinant-1 lift is unique for q = 7 and lies in G₂(7). Drop or reword the remark about −h.
7. Verdict item 4 and Computer-checked 4.7: these are measurements on particular random and annealed labellings. They
   are evidence about q ≤ 5, not a proof that no geometric labelling works there. The note words this correctly in §4
   ("stay open"); the summary could say "open" explicitly.

## 7. Files

`research/referee/omega-repair/` (README there has the commands):
- Hexagon and collineations: `gf.py`, `octo.py`, `buildhex.py`, `ghcheck.c`, `collin.py`.
- §3: `drg.py` (Lemma 3.1).
- Route counts: `myroutes.py`, `sweep.py`, `totals.py`, `perclass.py`.
- q = 7: `mytypes.py` (Lemma 4.3), `e2e43.py` (Lemmas 4.1, 4.3), `myperp44.py` (Lemma 4.4).
- Explicit graphs: `omg.c`, `omg_all.c`, `driver.py`, `convert_theirs.py` (§5.3, §5.4).
- `logs/`.
