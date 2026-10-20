# Lean brief: regularity, for the paper (AL Problem 4 asks for REGULAR graphs)

Master already has (see lean/Axioms.out.txt, lean/RegularAxioms.out.txt, lean/BipartiteDD/Plus2, ASq, GQST, Doubling):
Plus2.plus2 (diameter 3, max degree q+2, 2(q²+q+6) vertices, any projective plane with a frame), ASq.bound (Theorem A,
max degree q+2, diameter 4), GQST.regular_copy_graph, SingerC.regular5440, Doubling.*. Add, in that order (push after
each; new files under lean/BipartiteDD/Regular/):

1. General lemmas: (a) `IsRegularOfDegree` versions of the predicates (bipartite, every vertex degree exactly Δ,
   diameter ≤ D); (b) completion lemma: a bipartite graph with equal sides, max degree ≤ Δ, where the total deficits of
   the two sides are equal and each vertex's deficit ≤ s, and the deficit T is large (T > 2s(Δ+s+1) — see
   research/p4/regular/REPORT.md Theorem R step 4), extends to a Δ-regular bipartite graph by adding cross edges; adding
   edges keeps the diameter bound (master has ediam_le_of_le, colorable_of_add_edges). If the general Hall version is
   heavy, prove the special case used in 2 first. (c) twin lemma: deleting a vertex that has a twin (same neighbourhood)
   does not increase distances among the remaining vertices.
2. Diameter 3: Plus2 regular. research/plus2/coords/coords.tex (§ four-hat construction, step C7 and Table 1): exactly
   (q−1)(q−3) points and as many lines have degree q+1 and can be matched by non-incident pairs. Prove the regular
   version for every projective plane with a frame (a Hall/counting argument suffices; the explicit correlation δ needs
   coordinates — use PG(2,F) if you prefer and state it for finite fields F with |F| ≥ 4).
3. Diameter 4: Theorem A is regular: the AS(q) copy graph with the exact weighted 2-ovoid is (q+2)-regular (points
   already have q+2 lines; each line gets exactly 2 copies). State `ASq.bound_regular`.
4. Diameter 6, the abstract part of Theorem R: from the twin and completion lemmas, any bipartite graph with max degree
   Δ, diameter ≤ D, sides n1 > n2, whose larger side has at least n1 − n2 deletable twins (at most m−1 per twin class)
   and satisfies the deficit bound, yields a Δ-regular bipartite graph of diameter ≤ D on 2·n2 vertices.
Rules: `scripts/stop_check.sh` before each step; builds via `scripts/guarded.sh HOURS ...`; 5-hour limit; push hourly.
No `sorry`/`admit`/`axiom`/`native_decide` in finished files; only propext, Classical.choice, Quot.sound
(#print axioms in lean/BipartiteDD/Regular/Axioms.lean + .out.txt). Branch `lean-regularity`. Report: statements,
build result, axioms lines, what is left.
