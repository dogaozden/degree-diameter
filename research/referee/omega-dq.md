# Referee report: Gómez's ΩH_q and the D = 8 table entries (job referee-omega, 2026-10-26)

Opus referee session, branch `claude/omega-dq-referee-bzzlid`. Tools and logs: `research/referee/omega-dq/`.

Under review: `research/squads/cells/d12D8_table.md` on branch `claude/own-12-8-cell-ig5jhd` (commit 568fb4f), with the
earlier note `research/d12D8/r2/OMEGA_D9.md` (branch `claude/cell-12-8-search-qhi11t`) and the table audit's
relabelling result (`claude/table-audit-2-p7x6hn`, commit 28bea41). I read the thesis myself, checked the two theorems
line by line, and rebuilt everything with my own code: two hexagon builders, two ΩH builders, two BFS codes. No file of
the sessions under review was used, except the audit's labelling files for the one check in §3.4, which needs them.

## Verdict

| claim (write-up's numbering) | verdict |
|---|---|
| 1. The (12,8) value 4,650,100 is \|ΩH₉\|, 12-regular, bipartite, 27,900,600 edges | **Correct.** Thesis p. 46 lists "ΩH₉ : N(12,8) ≥ 4 650 100". My build: 4,650,100 vertices, all of degree 12, 27,900,600 edges, bipartite. The wiki table (fetched today) has 4,650,100 at (12,8), coloured "Graphs found by C. Delorme, J. Gómez, and J. J. Quisquater". |
| 2. ΩH₉ has diameter 9, not 8 | **"Not 8" is correct and proved** (Theorems 1 and 2, no computation needed); I reproduced it with my own code at the actual order. "Exactly 9" (both block types present) I reproduced at q = 7 and 9 by BFS from one vertex of each orbit class, which assumes that G₂(q) is transitive on points and on lines of H(q) (a standard fact I did not re-check), and exactly (all pairs) only at q = 3 and 5. With one block type the diameter is 10. |
| 3. A copy of K₁ is joined only to vertices with its own label t; no reading gives diameter 8 | **The reading is right**: the thesis says this explicitly in §2.8.9, which §2.9.3 cites for its copies of K₁. **"No reading" needs a qualifier**: no reading that keeps one labelling for all copies. A separate labelling per copy is not in the thesis, but it does give diameter 8 at q = 3 (I re-checked the audit's graph). |
| 4. Every D = 8 thesis value has eccentricity 9 | **Correct** for ΩH₅, ΩH₇, ΩH₈, ΩH₉, ΩH₁₁, ΩH₁₃: I rebuilt all six at their thesis orders and every K₁-vertex tested has eccentricity 9 in both readings. ΩH₁₁d (N(15,8) ≥ 14,978,080) is not defined in §2.9.3 and nobody checked it; the wiki's (15,8) entry is 14,172,480 = \|ΩH₁₁\|, so it is covered. |
| Theorem 1 | **Correct.** It is more general than stated: under reading 2 it refutes D ≤ D₁ + 2 for every B₁, not only the hexagons. |
| Theorem 2 | **Correct for q ≥ 7.** One sentence of the proof appeals to Theorem 1 where Theorem 1's hypothesis fails; the rest of the proof covers that case anyway. |
| Theorem 2's counting bounds | **Correct.** A + B + 1 < q⁵ holds exactly for q ≥ 7: 15,459 < 16,807 (q = 7), 25,482 < 32,768 (8), 39,763 < 59,049 (9), 85,491 < 161,051 (11), 162,627 < 371,293 (13). |
| §5 (attempts to beat 4,650,100) | Not refereed (outside this job). |

**What can be claimed** (my recommended wording):

> The table entries (10,8) 1,176,480, (11,8) 2,246,940, (12,8) 4,650,100, (14,8) 14,172,480, (15,8) 14,172,480 and
> (16,8) 36,201,060 are the orders of Gómez's graphs ΩH_q (thesis, UPC 1986, §2.9.3; q = 7, 8, 9, 11, 11, 13). The thesis
> claims diameter ≤ D₁ + 2 = 8 without proof. As defined there (every copy of the hexagon carries the same labels,
> and a copy of K₁ with label t is joined only to vertices labelled t), ΩH_q has diameter at least 9 for each of these
> q, under every reading of Figs 2.21a/b and every pairing of point labels with line labels (proof: Theorems 1 and 2;
> also checked by computation). The paper the table cites (Delorme, Gómez, Quisquater, "On large bipartite graphs")
> was never published, so these cells have no checkable graph of diameter 8.

What cannot be claimed: that no (Δ, 8) graph of these orders exists, or that no repair of ΩH_q works. Giving each
copy its own labelling is outside the thesis, but it reaches diameter 8 at exactly the thesis's order at q = 3 (the
audit's graph, re-checked here in §3.4) and at q = 2 (the audit's result; I did not re-check it). No such labelling is
known for q ≥ 4, and nobody has shown that none exists.

## 1. The thesis

I fetched `web.mat.upc.edu/francesc.comellas/delta-d/papers/Gomez1986-PhD-red.pdf` (8,989,821 bytes, a scan with no
text layer) and read thesis pp. 21–46 (§§2.7–2.9) at 110–220 dpi. Page offset: from thesis p. 33 on, PDF page = thesis
page + 6 (p. 43 is PDF 49, p. 46 is PDF 52), as the write-up says. Earlier pages are bound out of order: thesis p. 32
is at PDF 34, and pp. 28–31 are at PDF 35–38.

### 1.1 Text of §2.9.3 (pp. 43–45)

The write-up's translation is accurate. The key sentences, verbatim:

- p. 43: "En esta construcción, que da lugar a grafos bipartitos, también se toman, como en los Apartados 2.8.4 y
  2.8.9, copias de K₁ (vértices aislados)."
- p. 44: "Tomemos primeramente 5 copias de un grafo bipartito B₁ con diámetro D₁ par y 10 conjuntos de N₁ vértices
  cada uno. Cada 10 vértices —uno de cada conjunto— se unen a las copias de B₁ según muestra la Figura 2.21.a, de manera
  que su grado queda igual a dos. Ahora incrementamos dicho grado hasta 4, uniendo estos vértices a 5 copias de B₁
  según la Figura 2.21.b."
- p. 44: "El grafo bipartito así construido tiene N = 10·N₁/2 + 10N₁ = 15N₁ vértices, grado Δ = max{4, Δ₁+2} y diámetro
  D ≤ D₁ + 2." ("10 conjuntos de N₁ vértices" is a slip for N₁/2, as the write-up says; the count uses N₁/2.)
- pp. 44–45: "En general, si Δ₁ + 2 = 2α + β, α ≥ 2, β = 0, 1, se toman 5α copias de B₁ de manera que, utilizando
  cualquiera de las dos estructuras anteriores el grado de los vértices correspondientes a las copias de K₁ se
  incrementa hasta 2α. Entonces se obtiene un grafo bipartito, que denotamos por ΩB₁, con parámetros
  N = 10·N₁/2 + 5αN₁ = 5(α+1)N₁, Δ = Δ₁ + 2 y D ≤ D₁ + 2."
- p. 46 lists ΩH₅ N(8,8) ≥ 195 300, ΩH₇ N(10,8) ≥ 1 176 480, ΩH₈ N(11,8) ≥ 2 246 940, ΩH₉ N(12,8) ≥ 4 650 100,
  ΩH₁₁ N(14,8) ≥ 14 172 480, ΩH₁₁d N(15,8) ≥ 14 978 080, ΩH₁₃ N(16,8) ≥ 36 201 060.
- No proof is given. §2.8.2 (p. 30) says the proofs for this part are left out because, "aunque son largas, no ofrecen
  ninguna dificultad".

### 1.2 The figures

I checked Fig. 2.21a (p. 44) and Fig. 2.21b (p. 45) at 220 dpi. The write-up's description is exact. In (a), K₁-vertex
k sits on the star edge between copies k−1 and k+1, and k̄ on the circle arc between copies k+2 and k+3. In (b), k sits
on the arc between copies k+3 and k+4, and k̄ on the star edge between copies k−1 and k+1. In (b) the copies are named
B₁^{k̄}, which seems only to tell them apart from the (a) copies. Every copy has a dashed line with one dot on each side: an
outer dot on the circle and an inner dot at the star's corner. So each copy gives the ten vertices of one group one
vertex of each colour class, and every copy vertex gets two new edges.

The figures do not say which colour class the inner dot is. The write-up's reading 1 (inner = line, outer = point in
every copy, following "above the dashed line = class 0" from Figs 2.3, 2.6 and 2.18 applied to the top copy) and
reading 2 (k-vertices always on points, k̄-vertices always on lines) are both consistent with the drawings, and so is
any choice made per copy. The write-up's Theorem 2 covers all of these.

### 1.3 Labels: one labelling shared by all copies

The question is which vertex of each copy a group of ten uses. §2.9.3 itself does not say. The answer comes from the
notation the section inherits, and it is explicit:

- §2.7.1 (pp. 21–22): the colour classes V₁₀, V₁₁ of B₁ "están rotulados con los elementos del conjunto Z/n₁Z", and a
  vertex is written (s, i, j, t): label s in class j of copy t. All adjacency rules in §§2.7–2.9 ((2.14), (2.16),
  (2.18)) are stated in these labels, and every copy carries the same labels. The one proof written out in this part
  (Theorem 2.8.1, pp. 28–29) lists its paths in these shared labels ("primero se elige copia y luego vértice").
- §2.8.9 (p. 39), one of the two sections §2.9.3 points to for its copies of K₁, defines them as "(t, i),
  t ∈ {0, 1, …, n₁−1}, i ∈ {0, …, 4}", and Fig. 2.18 (p. 41) joins them as "(t,1,0,0,0) ∼ (t,0)" and so on: in every
  copy (B₁, k, h), the vertex with label t (in either class) is joined to a copy of K₁ with the same t.

So the write-up's reading in its §1.2 is right: a copy of K₁ with label t is joined only to point t and line σ(t) of
the copies the figure names, where σ is whatever pairing of point labels with line labels the labelling of V₁₀ and
V₁₁ by Z/n₁Z induces. The thesis fixes no σ, and Theorem 2 allows any σ.

**Could the thesis mean a different labelling per copy?** Not as a reading of the text, in my judgement:
- Nothing in §§2.7–2.9 permutes labels from copy to copy. Every rule there uses the same label in every copy.
- §2.9.3 cites §2.8.9 for its copies of K₁, and §2.8.9 states the same-label rule explicitly.
- The bound is claimed for every bipartite B₁ of even diameter. A labelling that works would have to depend on B₁, and
  the thesis gives no such labelling and no rule for finding one.

The only opening is that §2.9.3 alone ("cada 10 vértices —uno de cada conjunto— se unen a las copias de B₁ según
muestra la Figura 2.21.a") does not repeat the label rule. Someone reading that sentence without §§2.7–2.8 could treat
the choice of vertex pair in each copy as free. That is a different construction (a family, from which a good member
would have to be chosen), not what the thesis defines. A free relabelling is the only way the claimed bound could hold
for these q, and at q ≤ 3 one exists (§3.4). It should be described as a repair.

One more remark, which is not a reading. Under reading 2, Theorem 1 refutes D ≤ D₁ + 2 for every B₁ in one line. So
if the author had a correct argument in mind, it was not for reading 2. Reading 1 fails less obviously (it needs
Theorem 2's count, and that count fails for q ≤ 6), but it still fails: the computations at q = 3, 5 give 9 for every
σ tried (§3.3). The cited paper, which might contain a different wiring, was never published, so this cannot be
settled from the sources.

## 2. Theorems 1 and 2, line by line

### Theorem 1 (one label)

Statement: copies of B₁, plus new vertices each joined only to copies of a single vertex of B₁ (its label). If a new
vertex x with label t misses copy j and d_{B₁}(t, v) = D₁, then the copy of v in copy j is at distance ≥ D₁ + 3 from x.

Proof check. The only edges in ΩB₁ are copy edges and new-vertex edges (§2.9.3 adds no copy-to-copy edges, unlike
§2.8.4's Fig. 2.10). Labels project copy edges to B₁ edges. A copy vertex, then a new vertex y, then a copy vertex
projects to two vertices that both carry y's label, which is a stay that costs 2 edges. The path has to change copy (x
misses j), so it pays at least one stay. Its projection is a walk from t to v of length ≥ D₁. Total ≥ 1 + 2 + D₁.
**Correct.**

Applicability: under reading 2 every K₁-vertex is single-label, and so is every K₁-vertex under reading 1 when all
blocks have one type. A K₁-vertex has 2α neighbours and there are 5α copies, so it misses at least 3α copies. Every
vertex of a generalized hexagon has q⁵ opposite vertices. So diam ΩH_q ≥ 9 in these readings, for every q and every σ.
More generally, under reading 2 ΩB₁ has diameter ≥ D₁ + 3 for every B₁: the k-sets cover all points and the k̄-sets all
lines, so whichever class contains a pair at distance D₁, some K₁-vertex carries one of its labels.

### Theorem 2 (two labels)

Statement: ΩH_q, q ≥ 7, any bijection σ, any mix of blocks, any per-copy colour convention, copies keeping their labels.
Then some pair is at distance ≥ 9.

Proof check, step by step:
1. "If x meets one label only, use Theorem 1." **This step is not justified as written.** Theorem 1 assumes that
   *every* new vertex is single-label. In the mixed setting, other K₁-vertices can switch between point s and line σ(s).
   The gap is harmless: the counting below never uses that x meets both labels (it only lists the possible starting
   labels), so it covers this case with the same bound. Fix: delete the sentence, or say the count covers it.
2. Choice of target: x misses some copy j (2α neighbours, 5α copies). In copy j, take w in the class of x's neighbours.
   The graph is bipartite (a per-copy colour choice keeps it bipartite), so d(x, w) is odd and "≤ 8" means "≤ 7". The
   theorem should say "bipartite" in its hypothesis: a choice of colour per (copy, label) could break bipartiteness and
   the parity step. All readings of the thesis are bipartite, so nothing is lost.
3. Projection with switches: a pass through y with label s goes from {point s, line σ(s)} to {point s, line σ(s)}, so
   it is either a stay or a switch, and a switch is the bijection u ↦ σ-partner(u). **Correct.**
4. Parity: the path has length L = 1 + e + 2p (e copy edges, p ≥ 1 passes) with L odd and ≤ 7, so e is even, e ≤ 4,
   and p ≤ 3 − e/2. With w a line: starting at line σ(t) needs an even number of switches s, starting at point t an
   odd s. **Correct.**
5. Cases: start σ(t), s = 0 gives d(σ(t), w) ≤ 4, never opposite. Start σ(t), s = 2 gives p ≥ 2, so e ≤ 2, and at most
   B = Σ_{e₁+e₂+e₃≤2} s_{e₁}s_{e₂}s_{e₃} endpoints. Start t, s = 1 gives e₁ + e₂ ∈ {0, 2, 4} and at most
   A = Σ s_{e₁}s_{e₂} endpoints. Start t, s = 3 gives e = 0 and w = σ(t). There are no other cases (s ≤ p ≤ 3).
   "Walks that turn back reach no more than the shorter terms": a walk of length e reaches only distances e, e−2, …
   with the same parity, and all of those shorter shapes are already in the sums. **Correct.** (The sum for B also
   includes odd totals, which only overcounts.)
6. Symmetric case (w a point): swap t and σ(t). Points and lines have the same sphere sizes in H(q). **Correct.**

Counting bounds: `thm2_bound.py` evaluates A and B both from the sums over walk shapes and from the closed forms in
the write-up. They agree for every q from 2 to 16. Log: `logs/thm2_bound.txt`.

| q | A | B | A + B + 1 | q⁵ | q⁵ − (A+B+1) |
|---:|---:|---:|---:|---:|---:|
| 5 | 4,297 | 217 | 4,515 | 3,125 | −1,390 (fails) |
| 6 | 8,450 | 295 | 8,746 | 7,776 | −970 (fails) |
| 7 | 15,073 | 385 | 15,459 | 16,807 | 1,348 |
| 8 | 24,994 | 487 | 25,482 | 32,768 | 7,286 |
| 9 | 39,161 | 601 | 39,763 | 59,049 | 19,286 |
| 11 | 84,625 | 865 | 85,491 | 161,051 | 75,560 |
| 13 | 161,449 | 1,177 | 162,627 | 371,293 | 208,666 |

The bound holds from q = 7 on (the leading terms are 5q⁴ against q⁵). The margin at q = 7 is thin, but this is exact
integer arithmetic. The write-up prints the numbers for q = 7, 8, 9 only. Those are right, and so are q = 11 and 13.
The theorem actually gives more than one far pair: every K₁-vertex has at least q⁵ − (A + B + 1) vertices at distance
≥ 9 in every copy it misses.

The computations are consistent with the bound. Under reading 1 (σ = identity or random), the largest number of
odd-class opposite vertices within distance 7 of a K₁-vertex, in any copy it misses, was 7,562–8,039 at q = 7 (bound
15,459), 13,950 at q = 8 (25,482), 22,771–22,825 at q = 9 (39,763), 52,372 at q = 11 (85,491) and 104,225 at q = 13
(162,627).

## 3. Exact checks with my own code

Everything here is in `research/referee/omega-dq/`, written from scratch for this job.

### 3.1 The hexagons

- `hexgen.c` builds H(q) for prime q by a loop over pairs, and `hexgf.c` builds it for prime powers q ≤ 16 by a kernel
  computation. Both use the split-octonion model: points are the 1-spaces ⟨x⟩ of pure split octonions with x² = 0 (the
  quadric Q(6,q)), and lines are the 2-spaces ⟨x, y⟩ with xy = 0, with octonions written as Zorn vector matrices. My
  first attempt from memory of Tits' Grassmann equations gave wrong line counts (76 of the 364 points of H(3) on 4
  lines, the rest on 1), so I switched models. The table audit's `moore_build.c` uses p₆₅ = p₃₀ and p₄₆ = p₃₁, the
  two places where my memory had swapped indices.
- The two builders give identical line sets for q = 3, 5, 7.
- `bitapsp.c` runs a 64-source bit-parallel BFS from every vertex, with no symmetry. For each graph it checks
  regularity, bipartiteness, the diameter, and the girth. For girth, if every source has spheres of the largest
  possible size (q+1)q^{i−1} up to radius 5, a bipartite graph has girth ≥ 12.
- **H(7):** 39,216 vertices, 8-regular, bipartite, connected, **diameter 6, girth 12**. Sphere sizes from every vertex
  are 8, 56, 392, 2,744, 19,208, 16,807. The same checks pass for H(2), H(3), H(4), H(5), H(8), H(9), H(11) and
  H(13) (1,608,936 vertices, all pairs). A (q+1)-regular bipartite graph of diameter 6 and girth 12 on
  2(q⁶−1)/(q−1) vertices is a generalized hexagon of order (q, q).

### 3.2 ΩH₇ at the table order, reading 2

`omegaref.c` builds ΩH_q in memory from the figure description: copies 5B + i, K(t,k) and K(t,k̄), types a and b, and
either reading. It checks degrees, simple edges, connectivity and bipartiteness, then runs a plain queue BFS.
`omegacheck.py` is a second build in Python with tuple vertex names, wired by position in the figures (star or arc),
and its own BFS.

ΩH₇, reading 2, blocks ababa: **1,176,480 vertices** (25 × 39,216 + 196,080), 5,882,400 edges, all degrees 10,
bipartite, connected.

- BFS from the K₁-vertex K(t = 0, k = 0) (id 980400): **eccentricity 9**. Counts by distance 0–9: 1, 10, 84, 615,
  4,320, 30,240, 211,680, 305,270, 372,155, **252,105**. Both codes give the same profile.
- **Witness pair: K(0, k=0) and point 57 of copy 0, at distance 9** (ids 980400 and 57 in `omegaref`). Point 57 is
  opposite point 0 in H(7) (d_H = 6, by a separate Python BFS). K(0,0) meets copies 1 and 4 of each a-block and
  copies 3 and 4 of each b-block, so it misses copy 0.
- The 252,105 vertices at distance 9 are exactly the points opposite t in the 15 copies K(0,0) misses (15 × 7⁵), as
  Theorem 1 predicts. Nothing is at distance 10.
- The same holds for the k̄-vertex K(0, k̄=0): eccentricity 9, with lines opposite line σ(0) in the missed copies.

**Exact diameter at q = 7, with no assumption** (`omegaref ... exact`): the program checks edge by edge that the
rotation (copy 5B+i → 5B+i+1, K(t,k) → K(t,k+1), all blocks at once) and the swaps of same-type blocks are
automorphisms. It then runs BFS from every K(t, 0) and K(t, 0̄) and from every vertex of the first copy of each block
type: 117,648 sources, 64 at a time. Every vertex of ΩH₇ is in the orbit of one of them, so the largest eccentricity
is the diameter. Result: **diameter 9**, for reading 2 (ababa) and for reading 1 (ababa, one random σ). Every one of
the 117,648 sources has eccentricity exactly 9. Log: end of `logs/omega_q7.txt`.

Cheaper checks agree. BFS from one vertex of each of the 6 classes under H(7)'s automorphisms, the rotation and the
block swaps gives 9 for ababa and aabbb, and 10 when all blocks are of type a (K₁-vertex to K₁-vertex). 2,000 random
sources (1,644 copy vertices and 356 K₁-vertices) all have eccentricity exactly 9.

Reading 1 at q = 7 (σ = identity and two random σ, ababa and aabbb): every source tried (two K₁-vertices and four
copy vertices per graph) has eccentricity 9. Around 132,000–140,000 vertices are at distance 9 from a K₁-vertex, all in
copies it misses, and all opposite point t or line σ(t).

### 3.3 The other thesis values

All runs use `omegaref`, both readings (reading 1 with a random σ), and patterns mixing a and b. Log:
`logs/omega_q8_q9_q11_q13.txt`.

| thesis | table cell | vertices (built) | degrees | ecc of K(0,0), reading 2 | at distance 9 (= missed copies × q⁵) | ecc, reading 1 |
|---|---|---:|---|---:|---:|---:|
| ΩH₇ | (10,8) | 1,176,480 | 10 | 9 | 252,105 = 15 × 7⁵ | 9 |
| ΩH₈ | (11,8) | 2,246,940 | 11 (K₁: 10) | 9 | 491,520 = 15 × 8⁵ | 9 |
| ΩH₉ | (12,8) | 4,650,100 | 12 | 9 | 1,062,882 = 18 × 9⁵ | 9 |
| ΩH₁₁ | (14,8), (15,8) | 14,172,480 | 14 | 9 | 3,382,071 = 21 × 11⁵ | 9 |
| ΩH₁₃ | (16,8) | 36,201,060 | 16 | 9 | 8,911,032 = 24 × 13⁵ | 9 |

At q = 9 (blocks aaabbb, as in the write-up) my distance profile from K(0,0) is 1, 12, 124, 1,148, 10,350, 93,150,
838,350, 1,167,858, 1,476,225, 1,062,882, identical to the write-up's from its own code and hexagon model. All 6 class
representatives have eccentricity 9 (this step assumes G₂(9) is transitive on points and on lines; see below for the
exact run). Witness: K(0, k=0) (id 3985800) and point 91 of copy 0 (d_H(0, 91) = 6), at
distance 9.

q = 3 and 5 (all pairs, no symmetry, `logs/omega_q3_q5_allpairs.txt`, built by `omegalab.py` with every copy
labelled the same): ΩH₃ (14,560) and ΩH₅ (195,300, the thesis's (8,8) value) have **diameter 9** with both block types
present (aba, aab, abab, aabb) and **10** with one type. This holds in both readings and for σ = identity and two
random σ. My two builders give identical BFS profiles on reading 1 at q = 5 and on reading 2 at q = 7.

### 3.4 The audit's relabelled ΩH(3)

The audit's labelling files `q3_aba_LLL_G13.lab` and `..._Z5psi.lab` give every copy its own point and line labelling:
15 distinct point labellings, one of them the identity, and 15 distinct line labellings. They refer to the audit's
H(3), so I built that with their `moore_build h 3` and checked it with `bitapsp` (diameter 6, girth 12). I then wired
ΩH(3) with my own `omegalab.py` (reading 1 per block, inner = line), not their code. `bitapsp` gives 14,560
vertices, 6-regular, bipartite, **diameter 8** for both labellings. Log: `logs/audit_relabelled_q3.txt`. So a per-copy
relabelling of the thesis's wiring does reach D = 8 at q = 3, as the audit says. I did not check their q = 2 result.

## 4. Smaller points on the write-up

- §1.2 attributes the vertex notation to §2.8.1 (p. 27). It is introduced in §2.7.1 (pp. 21–22). §2.8.1 extends it
  with a copy-set index. Harmless.
- Verdict 3 ("No reading of §2.9.3 gives diameter 8") should say "no reading that keeps one labelling for all
  copies". The write-up's §5.1 says this itself, but the verdict line does not.
- Theorem 2: add "bipartite" to the hypothesis and drop the appeal to Theorem 1 (see §2).
- The earlier note `OMEGA_D9.md` says the bound "does not depend on how the copies are wired, only on the new vertices
  having degree < number of copies". That is too strong: it needs every copy to carry the same labels, and relabelled
  copies break it at q ≤ 3. The write-up already notes this.
- The write-up's other checkable statements agree with mine. Mixing both block types makes every two K₁-vertices share
  a copy (I checked the patterns by hand). The far vertices of a K₁-vertex under reading 2 are exactly missed copies ×
  q⁵. Reading 1 with random σ gives about 0.65M vertices at distance 9 at q = 9 (mine: 652,707–653,364).
- ΩH₁₁d: pp. 21–46 (§§2.7–2.9) do not define it; I did not search the rest of the thesis. The wiki uses 14,172,480 at
  (15,8), so ΩH₁₁d does not affect any table cell.
- (13,8) = 5,314,680 is also coloured Delorme–Gómez–Quisquater in the wiki but is not in the thesis. Nothing here
  bears on it.

## 5. Files

`research/referee/omega-dq/`: `hexgen.c`, `hexgf.c` (hexagons), `bitapsp.c` (all-pairs check), `omegaref.c` (ΩH_q
builder and BFS), `omegacheck.py` (second ΩH builder and BFS), `omegalab.py` (ΩH with per-copy labels, edge-list
output), `thm2_bound.py`, `README.md` (commands), `logs/`.
