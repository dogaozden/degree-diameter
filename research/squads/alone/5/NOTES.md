# Squad alone-5: modify the PG(4,3) flag graph (delete a structured set, add more vertices)

Haiku worker 5 of 8, no Opus direction. Goal: bipartite, max degree 16, diameter 5, more than 31,460 vertices.
Region: delete vertices or edges of the flag graph, add more than were removed.

**Result: no graph above 31,460 was found, and nothing is saved to `research/frontier/sols/`.** Every candidate I
built that added vertices had diameter 6. I also have evidence that the flag graph is locally rigid, so the
edge-level changes I tried cannot reach a gain. I have not ruled out every structured change.

## Setup and baseline

- `scripts/flags_pg43.py` rebuilds the flag graph: 15,730 + 15,730 vertices, 251,680 edges, 16-regular.
  Checked with `research/lifts/coordinator_check/apsp.c` (no symmetry assumed): `n=31460 degree 16 bipartite diameter=5`, VALID.
- Distance profile is identical from every vertex (checked on several sources). From an A-vertex: B-vertices at
  distance 1, 3, 5 are 16, 2268, 13446. From a B-vertex: A-vertices at 1, 3, 5 are the same counts. Same-side
  vertices at distance 0, 2, 4 are 1, 204, 15525, so every same-side vertex is within distance 4. The diameter is
  tight in the sense that most opposite-side vertices are at distance exactly 5.

## Findings

1. **Neighbourhoods dominate.** For an A-vertex a, the 16 B-neighbours of a radius-3 dominate A (every A-vertex is
   within distance 4 of a). Greedy search for radius-3 dominating sets of A from B-centres needs 26 centres
   (`scripts/dom.py`). Annealing from random starts with 16 centres stalls at about 380 to 420 uncovered A-vertices
   (`scripts/sa_cover.py`, 2 seeds). I found no 16-set cover that is not a neighbourhood.

2. **Every edge is rigid.** Deleting an edge (u,v) pushes 729 same-side vertices of u from distance 4 to
   distance 6. Those are the targets reached only through v. Over 12 random edges, plus the edge at a*, each cone
   has size 729 and no other neighbour of u covers any of it (`scripts/cones.py`, `scripts/lost_cover.py`). Deleting
   one random edge already gives diameter 6 (control, `one_*.e`).

3. **Single 16-edge exchange fails.** A new A-vertex x adjacent to 16 freed B-vertices and a new B-vertex y adjacent
   to 16 freed A-vertices gives 31,462 vertices. Requiring the 16 removed edges to form a perfect matching between
   the two sides is the only way to free the slots at no extra cost. The matchings do not exist in practice:
   between N(b*) and N(a*), the maximum matching is 5 for adjacent pairs and 0 or 1 otherwise (`scripts/mstats.py`). Annealing over general 16-edge sets reaches 873 uncovered (`scripts/sa_match.py`).

4. **Twin insertion has diameter 6.** Let x be a new vertex with N(x) = N(a*) and y a new vertex with N(y) = N(b*).
   Each b in N(a*) and each a in N(b*) loses one edge to a free partner (`scripts/twin2.py`). Result: 31,462 vertices,
   diameter 6. The damage is concentrated at a*, b*, x, y (about 700 to 1,400 targets pushed to distance 6 each), with
   about 4 extra violations per ordinary vertex. Adding a repair matching between the 16 deficient A and 16 deficient
   B vertices restores 16-regularity (31,462 vertices) but leaves diameter 6 (`scripts/repair.py`).

5. **Partner choice cannot fix the hubs.** With N(a*) as the x-side cover, the partners of N(a*) lie within distance 2
   of a*, and they radius-3 cover at best 540 B-vertices (`scripts/sa_side.py`). A gain needs its partners spread out,
   and the cone argument in (2) says they cannot be.

## Interpretation

Each vertex in the flag graph gives up 729 distance-5 targets per removed edge, and only that edge's other endpoint
can restore them. So a degree-preserving edge deletion is paid for at both ends, and a new vertex needs a 16-set that
dominates the far side, which in this graph means a full neighbourhood. Together these make single-edge and
twin-style gains infeasible here. A gain would need a larger gadget that removes a whole neighbourhood or ball and
rebuilds it, with the lost cones covered by new paths through the gadget. I did not test that; it is a candidate
for a later round. Note that the 729-cone argument shows edge deletion is locally costly, not impossible: a gadget
that recovers those cones through new length-5 routes could still work.

## Caveats

- The annealing and greedy numbers are heuristic. "No cover found" does not prove none exists. The rigidity
  claim is checked on 13 edges, not all 251,680.
- The 2013 table value (27,300) is below the 31,460 flag graph, and I did not try to beat it with other families.
- Large intermediates (the 247 MB ball matrix, edge lists of 2 to 3 MB) stay in the working scratchpad; they are
  rebuilt by `scripts/cov.py base.e` (writes `C3.npy`) and `scripts/flags_pg43.py`.

## Scoreboard

`scoreboard.jsonl` has one line per serious attempt. Valid graphs are only the baseline. Scores for failed covers
are costs (uncovered vertices or centre counts), and the idea field says which.

## Reproduce

```
python3 scripts/flags_pg43.py base.e                 # 31460 flag graph
gcc -O2 -o apsp research/lifts/coordinator_check/apsp.c && ./apsp base.e 16 5
python3 scripts/cov.py base.e                         # writes C3.npy (ball-3 matrix)
python3 scripts/twin2.py base.e tw_1.e 0 0 1 any && ./apsp tw_1.e 16 5   # diameter 6
```
