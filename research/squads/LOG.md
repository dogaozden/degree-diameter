# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25, cell-16-7 (Opus, cloud session_01SiFUa6yem3dNwLbHS2XdrE, resumed job), round r2: orbit-graph independent sets for the typed-level (16,7) graph

Goal: (16,7). Before the round Opus found the typed-level construction (research/squads/cells/d16D7.md): five copies of
H(13) with levels 1, 3 read as the dual hexagon, identity matchings on six of the ten transitions, so the freed sets only
need to be non-collinear (points) / non-concurrent (lines), and n = 4,022,340 + 2·61·K with K = min(K_pts, K_lines), the
sizes of independent sets in two orbit graphs (orbits of an order-61 collineation; 6,504 vertices, degree ~177). Opus's
60 s ILS gave 224 / 227 (n = 4,049,668). Brief: research/squads/d16D7_r2/BRIEF.md (scorer ogscore.py). Launched 03:44 UTC.

Cards: c1 ARW iterated local search · c2 k-fixed penalty tabu · c3 simulated annealing · c4 min-degree greedy
multistart + (1,2)-swaps · c5 search invariant under an order-3 automorphism (from an order-183 collineation), then
polish · c6 LNS with exact branch-and-bound refills · c7 wildcard (memetic) · c8 geometric wildcard.

Best per card (points / lines, all re-scored by Opus with ogscore.py): c1 234 / 233 · c2 235 / 237 · c3 232 / – · c4 221 /
221 · c5 – · c6 229 / – · c7 231 / 231 · c8 **240 / 240** (sets invariant under a group of order 9 on the orbit graph, h of
order 183 and a Frobenius map, annealed in the 573/588-vertex quotient for 8 s, then expanded).

Kept: c2's 235/237 gave the first verified record, **4,051,254** (with 2 orbits of local-duality surgery on the non-friendly
transitions; apsp_autw VALID). Then c8's symmetric quotients: Opus built the quotients for all four order-3 subgroups and
the order-9 group (cells/d16D7/ogquot.py) for round r3. Lesson again: the structured (symmetric) search beat every
generic local search, in seconds. Exact bipartite merging of pairs of good solutions (bimerge.py) added nothing: the
solutions share only 4-28 orbits.
