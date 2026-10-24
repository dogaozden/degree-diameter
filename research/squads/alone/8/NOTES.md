# squad-alone-8 (wildcard) notes

Worker 8 of the squad-alone-8 experiment: Haiku workers without Opus direction, goal a bipartite
graph with max degree 16, diameter 5, more than 31,460 vertices. Region: wildcard (another geometry,
quotient search, duplication tricks). Result: **no graph beyond 31,460 found.**

## What was tried

1. **Duplication: 2-fold cover of the 31,460 flag graph. Impossible.** The base graph
   (`research/theorems/coordinator_check/flags_pg43.py`) has, for each source, about 74% of same-side
   vertices joined by exactly one plain walk of length ≤4 (walk counts from three sources:
   11,664 of 15,730 same-side vertices have count 1). A voltage lift over any group of order m ≥ 2
   needs m distinct walk voltages for each such pair, so no lift of this base keeps diameter 5.
   Scoreboard: score 0.742 (fraction of same-side pairs with a unique walk).

2. **Z_121 quotient (Singer cycle).** The PG(4,3) flag graph is a Z_121 voltage lift of a 130+130
   base (orbits of the order-121 Singer subgroup act freely). `singer_base.py` rebuilds that base,
   `expand_lift.py` expands it, and apsp.c confirms the 31,460-vertex lift is valid (degree 16,
   bipartite, diameter 5). This validates the framework; it is not a new record.

3. **Annealing over Z_121 voltage lifts, random starts** (`lift_sa.c`, 60,000 steps, T 30 → 0.5):

   | K (orbits/side) | vertices | final cost | fraction uncovered |
   |---|---|---|---|
   | 100 | 24,200 | 13,874 | 0.29% |
   | 110 | 26,620 | 28,618 | 0.49% |
   | 120 | 29,040 | 51,336 | 0.74% |

   Cost counts (source, target lift vertex) pairs with no walk of length ≤5 of the right voltage.
   Even random coverage at these sizes leaves about 0.5% of same-side pairs uncovered; annealing
   reduces that by only a few times within 60k steps.

4. **Warm start at K=131 (31,702 vertices, would beat 31,460).** `split131.py` splits 16 matched edges of the
   flag base to add one orbit per side. Initial cost 85,922 (about 1%); annealing reached 80,412
   (0.97% of pairs) after 60,000 steps. Far from zero.

## Why local search is not expected to get there

Walk-counting: from a vertex, there are 54,241 walks of length ≤4 that can reach same-side vertices, so
a random-like covering of N_side vertices has average multiplicity λ = 54,241/N_side. Random covering
needs λ ≳ 10 to be complete, which means N_side ≲ 3,000. Haar/lift records found by search sit near
λ ≈ 6 (N_side ≈ 9,000). The flag graph has N_side = 15,730, i.e. λ ≈ 3.4, and is exactly complete,
so it is algebraic structure, not a search product. Group-quotient searches with other groups have
the same λ, because λ = 54,241/N_side for any group. Local search at λ ≈ 3.4 would have to remove
about 3% random misses to zero, which the annealer did not come close to doing.

## Not attempted

- A non-abelian quotient (e.g. Z_121 ⋊ Z_5, order 605, 27 orbits = 32,670 vertices). The same λ argument
  applies. The table-based annealer would be about 100× slower per evaluation than the abelian one.
- SAT/ILP on the quotient: the walk-constraint encoding has about N²·(walks) clauses, which was not
  built.
- Other geometries of degree 16. Within PG(4,3), the (point<plane)/(line<solid) flag structure is
  the only regular side of size >15,730; point–solid and point–line flag types are not regular at
  degree 16.

## Files

- `lift_sa.c`: Z_M voltage-lift annealer (abelian, M ≤ 128).
- `singer_base.py`: Z_121 Singer base of the PG(4,3) flag graph (130+130 orbits).
- `expand_lift.py`: base file → plain edge list for apsp.c.
- `split131.py`: K → K+1 warm start.
- `scoreboard.jsonl`: one line per serious attempt.
