# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-13-7 (Opus, cloud session), round 1: largest partial ovoid of Q(6,11)

Goal: (13,7), table 1,062,936 = 3 copies of the H(11) incidence graph + one matching. Opus found before the round
that the matching can be any bijection σ, and that removing the matching edges at a set R of pairwise opposite points
where σ is a local duality frees 6|R| slots for 2|R| new vertices (research/d13D7/REPORT.md, tri.c; greedy R ≈ 100
gave 1,063,140). Opposite points of H(11) are the non-orthogonal points of Q(6,11), so the round asked for the
largest partial ovoid of Q(6,11) (scorer research/d13D7/tools/oppcheck). Baselines: greedy ~100, elliptic 3-space
section 122, Opus ILS 133. Brief: research/squads/d13D7_r1/BRIEF.md.

Cards: c1 stronger ILS (tabu, plateau swaps) from the 133-set · c2 fixed-k penalty annealing · c3 union of parallel
affine lines (fibration), reduced to a clique in a class graph on F_11^4 · c4 unions of orbits of cyclic subgroups
of O(7,11) · c5 LNS with exact MIS repair · c6 pieces of elliptic sections + ILS · c7 wildcard · c8 theory-first
algebraic sets (polynomial graphs, repair).

Best per card (all re-checked by Opus with oppcheck; the top ones also with an independent numpy check):
c1 137 · c2 136 · c3 **243** (22 lines + e4, Python tabu) · c4 256 (orbits of an order-61 element, from its
results file; card did not report) · c5 134 · c6 282 (ILS seeded with a 136-set from 16 pooled elliptic sections) ·
c7 174 (min-degree greedy; not reported) · c8 **320** (took the same line-cylinder idea as c3 independently and
used a C clique search: 29 lines + e4).

Kept: the fibration (c3, c8): R = e4 + k conics through e4 whose planes share a tangent line, k = a clique in the
strongly regular graph Cay(F_11^4, {c^2 - 2a^2 - bf non-square}) (Delsarte bound 102). 320 points give 1,063,576
vertices (built by research/d13D7/build_d13D7.py; full all-pairs check running). Lesson: every structured method
(fibration, orbits, seeded ILS, min-degree greedy) beat the random-start local searches (133-137) by 1.3-2.4x.
Next: round 2 on the clique number of that graph (each clique vertex = 22 graph vertices).
