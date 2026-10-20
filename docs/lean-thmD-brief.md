# Lean brief: Theorem D, slice 2 (Hermitian spread, Delorme's levels on H(q), whiskers)

Master now has: lean/BipartiteDD/Hexagon/ (Qf, Tits equations, SPt, HLine, φ into the split octonions, isHPair_iff,
finrank_plane, card_* counts, genPolygonGraph_hexagon : GenPolygonGraph (incGraph hexInc) 6, odd q) and
lean/BipartiteDD/Doubling/ (delorme_levelled_polygon: levels A0 ⊇ A1 ⊇ …, hypotheses (a), (b), ForestDiam (n−2)).
Read docs/lean-hexagon-status.md and research/p4/hats/REPORT.md §4 (Delorme's construction, Theorem 3, Theorem 4 with
its proof steps 1–4 and the closed-form identities in research/p4/hats/proof/verify_closed*.py).

Targets, in order (folder lean/BipartiteDD/HexagonD/; push after each):
1. The hyperplane Π: x0 + c·x4 = 0 with −c a nonsquare; S = H(q)-lines in Π. Prove S is a spread of Π ∩ Q (every
   singular point of Π on exactly one line of S; Report §4 Theorem 4 proof step 1) and that distinct lines of S are
   opposite (distance 6 in the incidence graph); |S| = q³+1.
2. Delorme's levels for v ∈ S (A2 = {v}, A1 = {v} ∪ points(v) ∪ (S∖v), A0 = A1 ∪ lines through points of v ∪ points of
   S-lines): verify hypotheses (a), (b) and ForestDiam 4 of delorme_levelled_polygon, giving Delorme's 1985 bound
   n_b(q+2,6) ≥ 2(q+1)(q⁴+q²+1) + q⁴+4q³+q²+4q+10 for odd q (and m-ary for q+m).
3. Theorem 3 (whiskers): adding any set W of lines opposite v, not in S, with no free point on two of them, keeps (a),
   (b), ForestDiam 4; so the bound grows by (m−1)|W|.
4. Theorem 4 (exact whiskers): the explicit W from the spreads S_z and an irreducible binary cubic G has
   |W| = q²(q²−1). This is the hardest part; split it into the report's steps 1–4 and state each as a lemma first.
   If time runs out, leave clean statements and a plan in docs/lean-thmD-status.md.
5. Combine with Regular.regular_of_twin_classes for Theorem R if 4 is done.
Rules: `scripts/stop_check.sh` before each step; builds via `scripts/guarded.sh HOURS ...`; 5-hour limit; push hourly.
Finished files: no `sorry`/`admit`/`axiom`/`native_decide`; only propext, Classical.choice, Quot.sound (Axioms.lean +
.out.txt in the folder). Also run `lake build` of the whole library once at the start (master merged hexagon and
regularity without a combined build) and report the result. Branch `lean-thmD`.
