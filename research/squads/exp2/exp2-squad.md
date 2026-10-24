# exp2-squad: the three D = 7 cells (Opus + Haiku squad)

Job "exp2-squad", 2026-10-24, one Opus session plus Haiku subagents (haiku-squad skill), cloud container with 4 cores.
Start 16:56:02 UTC (research/squads/usage/exp2-squad.start). Budget log: research/squads/usage/exp2-squad.jsonl.

## Result

All three cells are beaten. Every graph below was written as an edge list and checked by
research/lifts/coordinator_check/apsp.c (all-pairs BFS: simple, bipartite, max degree, exact diameter).

| cell | table | best VALID (this job) | ratio | graph | check |
|---|---|---|---|---|---|
| (7,7) | 23,436 | **BEST77** | RATIO77 | H(5) × Z3, K77 freed pairs + 2K77 hubs | CHECK77 |
| (9,7) | 117,648 | **BEST97** | RATIO97 | H(7) × Z3, K97 freed pairs | CHECK97 |
| (11,7) | 398,580 | **BEST117** | RATIO117 | H(9) × Z3, K117 freed pairs | CHECK117 |

FINAL_BUDGET

## What the table values are, and why Haar graphs were not the way in

The three table values decode exactly as 3·|H(q)| with Δ = q+2 (H(q) the split Cayley hexagon, |H(q)| = 2(q⁶−1)/(q−1)):
23,436 = 3·7,812 (q = 5), 117,648 = 3·39,216 (q = 7), 398,580 = 3·132,860 (q = 9). The wiki credits D = 7, Δ ≥ 6 to
Delorme, Gómez and Quisquater. Earlier sessions had already shown that these cells lie above the first-moment ceiling
for random-like and orbit-symmetric Haar graphs (STRUCTURE.md on the structured-search branch: (7,7) and (9,7) screened
and dropped), so this job did not run Haar searches at all.

## The construction (research/squads/exp2/hexd7/README.md has the proofs)

1. **The table construction works for any matching.** X(M): three copies (levels i ∈ Z3) of H(q); each point p at level
   i gets one extra edge to the line M(p) at level i+1, for a bijection M from points to lines. Max degree q+2. Diameter 7
   for EVERY bijection M: from a point (p,0), level 1 is reached by the extra edge and then a hexagon path (≤ 1+5 to
   points, ≤ 1+6 to lines); level −1 by a hexagon path to the line M(x) and its extra edge down to x (≤ 5+1); lines are
   symmetric. This freedom is what makes the improvement possible.
2. **Hub vertices: +2 per freed pair.** Delete the three extra edges of a point p (and so of the line M(p)), add a
   line-side hub z ~ (p,0),(p,1),(p,2) and a point-side hub z' ~ (M(p),0),(M(p),1),(M(p),2). All routes of the proof
   survive except those that start or end at the freed vertices, so the graph has diameter 7 iff (p,0) still reaches all
   of level 1 and (M(p),0) all of level −1. The hub covers everything within hexagon distance 4 of p; the points
   opposite p need other routes, e.g. (p,0) ~> (u,0) -> (M(u),1) -> (x,1) with u at distance 4 from p and x on M(u).
3. **An exact algebraic cover for one pair.** Take M(p) = l through p, S'(p) = points at distance 4 from p not via l
   (q⁴ of them) and S(l) = lines at distance 4 from l not via p (q⁴). Every point opposite p lies on exactly one line of
   S(l), and every line opposite l passes through exactly one point of S'(p). So ANY bijection S'(p) -> S(l) satisfies
   both conditions: one freed pair needs no search at all (this gave (11,7) instantly).
4. **Many pairs.** Hubs of the same side must stay within distance 6 of each other, so they are linked by a hub graph on
   their spare degree (q−1 per hub): the incidence graph of PG(2,q−2), PG(2,3), PG(2,4), GQ(3,3), or random sparse
   bipartite graphs. The covers of different pairs compete for the same points, so M is chosen by a local search on an
   incremental route-count proxy (type-4 and type-2 routes; proxy 0 implies the freed sources are fine), with a
   type-2 greedy pre-pass, best-of-k moves, and pair dropping to salvage near misses. Every new vertex needs a neighbour
   in each of the three levels, so new vertices ≤ (freed slots)/3 = 2 per freed pair: hubs are optimal in this family.

## What was tried (in order) and what worked

TIMELINE

## The squad

SQUAD

## Limits and honest notes

- The gain is +2 per freed pair, and the number of pairs is limited by how many extra edges the covers can share. At
  q = 5 a pair needs roughly 200 aimed extra edges out of 3,906; runs with K = 40 stalled. Ratios over the table are
  therefore small (+0.1–0.3 % at (7,7), much less at q = 7, 9).
- Four copies (Z4, +33 %) are hopeless (squad card r1/c8: ~390 uncovered targets per source after local search).
- The graphs are not Haar graphs, so build_haar2.py does not apply; the solution files (.sol, format in d7hex.c) give
  the hexagon q, the freed points, the hub graph and M; `d7hex edges` rebuilds the edge list from them and hexgen.c's
  H(q), and apsp.c checks it. The coordinator should rebuild independently.
