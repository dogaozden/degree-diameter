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

## 2026-10-24, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH, resumed job), round 2: beat 320 pairwise-opposite points of H(11)

Goal: (13,7); the record graph is 1,062,936 + 2|R| with R a partial ovoid of Q(6,11) (pairwise opposite points of H(11)).
Start: |R| = 320 (round 1), whose graph 1,063,576 this session checked all-pairs (VALID). Brief:
research/squads/d13D7_r2/BRIEF.md (explicit coset graph Cay(F_11^4, {s^2+3c^2+8bf non-square}), lifter fiblift.py,
scorer oppcheck; c8 scorer linestar_check). Launched 22:28 UTC, 8 Haiku cards.

Cards: c1 DLS-MC max-clique in the coset graph · c2 other fibrations (square-class direction, multi-direction) · c3
fixed-k tabu for a 30-clique · c4 unions of orbits of cyclic subgroups of O(7,11) · c5 cliques invariant under small
similitude groups · c6 LNS with exact repair seeded from the 320 set · c7 wildcard (annealing on the affine model) ·
c8 line-stars (the line side of a relaxed surgery with distance-4 "stars").

Best per card (Opus re-checked the top ones with oppcheck and a numpy check): c1 29-clique = 320 (39,089 distinct
29-cliques, never 30; from its log) · c2 320 (square class only 20 lines; tangent direction pairs give nothing) ·
c3 320 · c4 **364** (orbits of an element of order 44; 55 -> 362, 110 -> 340) · c5 320 · c6 **397** (removing e4 frees
the 90 points at infinity blocked only by e4, 62 of them pairwise opposite: 381; LNS then 397) · c7 319 · c8 128 lines
in 121 stars (far below 320).

Kept: LNS (c6) and orbit unions (c4). 397 points give **(13,7) 1,063,730**, built by build_d13D7.py and checked
all-pairs by Opus (apsp_wide, VALID). c8 plus Opus's coherence test (relax/cohere*.c: for lines the "forbidden"
choices across a star are incoherent, for points they are coherent through the GQ Q(4,q)) close the star relaxation
for q = 11. The clique number of the coset graph looks like 29. Lesson: the structured record was not 1-swap optimal;
the exact-repair LNS found the swap that the clique searches could not see.
Side results the same evening, using the same theorem at other q (Opus, not the squad): (11,7) 400,040 (ovoid of
Q(6,9)), then 406,298 (explicit duality of H(9)); (9,7) 117,992; (7,7) 23,552.
Next: round 3 on beating 397 (LNS variants, deeper orbits, crossover, ARW, region blocks, fibration + infinity).
