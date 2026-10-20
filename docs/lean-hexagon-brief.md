# Lean brief: the split Cayley hexagon H(q) and the start of Theorem D (slice 1 of several)

Goal of the whole project: Theorem D (research/p4/hats/REPORT.md §4, Theorem 4; research/geometry/ when it lands) in
Lean for every odd prime power q. The general part is already on master: lean/BipartiteDD/Doubling/ (Delorme's
levelled doubling, Theorem 1; the hat lemma for `GenPolygonGraph`). This slice builds the geometry.

Slice 1 targets (folder lean/BipartiteDD/Hexagon/; push after each):
1. The parabolic quadric Q(6,q): Q(x) = x0x4 + x1x5 + x2x6 − x3² on Fin 7 → F, F a finite field of odd characteristic;
   singular points; the H(q) lines as the totally singular lines whose Grassmann coordinates satisfy Tits' equations
   (use the same equations as research/gh6/gh_build.py and research/p4/hats/hexbig.py — read them; state them as a
   predicate on pairs of points spanning the line).
2. The incidence graph of H(q) and the counts: (q⁶−1)/(q−1) points, the same number of lines, q+1 lines on each point,
   q+1 points on each line. If a full proof is heavy, prove the local structure (q+1 lines per point) first.
3. Stretch: `GenPolygonGraph (incidence graph of H(q)) 6` (girth 12, diameter 6). This is the hard part; if you get
   partway, leave clean, documented lemmas and a plan in docs/lean-hexagon-status.md. Do NOT use sorry in files that
   the main library imports; work-in-progress files may contain sorry only if they are not imported by
   lean/BipartiteDD.lean and are listed in the status note.
Also: for q = 3 and q = 5 a decide-free sanity check is welcome (e.g. the counts by computation with `decide` on small
Fin types if feasible, never native_decide).

Rules: `scripts/stop_check.sh` before each step (STOP → commit, push, end); builds through `scripts/guarded.sh HOURS ...`;
total time limit 5 hours; push every hour. Finished files: no `sorry`, `admit`, `axiom`, `native_decide`; only
propext, Classical.choice, Quot.sound (#print axioms lines in lean/BipartiteDD/Hexagon/Axioms.lean + .out.txt).
Branch `lean-hexagon`. Report: definitions, theorems, what is left, build result, axioms lines.
