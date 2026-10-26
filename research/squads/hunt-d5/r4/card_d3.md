# Card d3 (round 4)

Read ../r1/PREAMBLE.md, ../r3/PREAMBLE.md and ../r4/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r4/d3/ (create it).

(6,5) NEW CELL, per-edge F₂⁴ route-chart lifts (tools/pelift.c, degree 6, n = 32m; m ≥ 22 beats 684). On 4-cycle-free controllers a few fibres keep a diagonal gap; controllers with a 4-cycle at every vertex stop near m = 16. Try mixed controllers: cubic bipartite, same-side distance ≤ 4, with 4-cycles at as many vertices as possible (adapt tools/ctrl.c: e.g. W4=1 and write the best graph even at cost > 0), m = 18, 20, 22; run pelift (60–120 s, DIAG=1) and report which vertices fail and the best cost per m.
