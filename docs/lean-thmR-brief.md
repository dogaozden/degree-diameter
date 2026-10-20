# Lean brief: Theorem R instance (regular diameter 6, paper Theorem 6.12) for odd q

Master has: Regular.regular_of_twin_classes (abstract: twin classes + deletion + completion ⇒ Δ-regular bipartite graph
of diameter ≤ D on 2·|α| vertices; lean/BipartiteDD/Regular/TheoremR.lean), and HexagonD.theoremD / theoremD_two with
the levelled doubling of H(q) plus the exact whisker set (lean/BipartiteDD/HexagonD/, TheoremD.lean, Delorme.lean;
the doubled graph comes from Doubling.delorme_levelled_polygon). Paper: research/geometry/geometry.tex Lemma 6.10
(repeated lines), Lemma 6.11 (completion), Theorem 6.12; research/p4/regular/REPORT.md Theorem R.

Target (folder lean/BipartiteDD/HexagonD/Regular/; push after each step):
1. Expose the doubled+whiskered graph of theoremD as an explicit bipartite relation r : α → β (points side α, lines side
   β) with |β| − |α| = (m−1)·m·(q³−q+m), max degree q+m, ediam ≤ 6. (Refactor theoremD minimally if it only gives an
   existential; keep its statement unchanged and add a new lemma.)
2. Twin classes on the line side: for an S-line ℓ ≠ v the m versions ℓ^{a·}, and for v the versions v^{ab·}; prove
   they have equal neighbourhoods (the class map cls), there are mq³+m² classes of size m.
3. Choose S (the deleted line versions, at most m−1 per class, exactly the excess), and check the hypotheses of
   regular_of_twin_classes: degree deficits ≤ s := m−1 (a point loses at most m−1 neighbours from one class; whisker
   versions have degree q+1) and the large-deficit condition 2s(Δ+s+1) < T (T ≥ (m−1)·m·q²(q²−1)).
4. `theoremR : ∃ G : SimpleGraph (Fin (2*(q+1)*(q^4+q^2+1 + (m−1)*(q^3+m+1)))), IsBipartiteRegDiam G (q+m) 6` for odd q,
   m ≥ 2 (also state m = 2: 2(q+1)(q⁴+q³+q²+4)). If time runs out, push clean statements and a status note.
Rules: `scripts/stop_check.sh` before each step; builds via `scripts/guarded.sh HOURS ...`, build heavy modules one at a
time (the full build OOMs in parallel); 5-hour limit; push hourly. No `sorry`/`admit`/`axiom`/`native_decide`; only
propext, Classical.choice, Quot.sound (Axioms.lean + .out.txt in the folder). Branch `lean-thmR` from origin/master.
