# r2d NOTES (Haiku worker r2d, card r2d: Moore-tree completion)

Start: 2026-10-31 17:25:28Z (date -u). Stop about 19:25-19:40Z.

## Plan (first draft, 17:30Z)
Moore-tree view: for a root vertex v in A the 127 even NB walks of length <= 6 must cover all m same-side vertices,
so the walk tree has exactly delta = 127 - m collisions (42 at m = 85). Every collision is a short cycle through v, so
the tree is decided by which cycles exist. Card r2d asks for a structured tree-completion search.
Idea I will test first (not yet on any card): an involution sigma that colour-preserves the bipartition and fixes f
EDGES pointwise (each fixed vertex has 1 fixed neighbour and 1 swapped pair). The root edge of the Moore tree is then
fixed, the tree is symmetric, and the search space halves. Moves: equivariant 2-switches (remove e, f, sigma e, sigma f;
add a-d, c-b and their sigma images). Cost: far (unordered pairs at distance > 7). Search: simulated annealing and tabu.
c6 covers side-swapping involutions (polarity); c5 covers order 3; c3/c4 cover free groups. Fixed-edge involutions are
not covered by any card.

## 17:36Z results so far

Code: r2d/inv.c (equivariant SA/tabu, sigma = involution, f fixed edges; env INIT_EDGES + INIT_SIGMA to start from a file),
r2d/nb1.c (exhaustive depth-1 equivariant neighbourhood), r2d/ins170.py (orbit insertion into C168.1), r2d/farpairs.py.
Moore accounting used: for an A-vertex, 127 even NB walks of length <= 6, need 85 covered, so excess R(v) = 42 + (# same-side
vertices missed). far = (1/2) sum_v (R(v) - 42). Check: far-46 graph has 94 vertices with R = 42, 60 with 43, 16 with 44.

1. C168.1 colour-preserving involutions (c5/out/aut168.txt, 504 automorphisms): 3 of them, all FREE (no fixed vertices).
   Orbit insertion of a FIXED edge (a,b) (n 168 -> 170, f = 1): remove edge orbit {xy, sx sy}, add a-y, a-sy, b-x, b-sx, a-b.
   Scores (378 insertions): 252 give far 46, 126 give far 64. (The 46 is the same floor as c1.)
2. Exhaustive depth-1 equivariant neighbourhood of the symmetric far-46 graph (nb1, 62084 valid moves, 0.34 s): best 46,
   1108 neighbours at 46, none lower. Strict local floor for single equivariant 2-switches.
3. Equivariant SA from random, f = 1: n=150, 120 s, T 8 -> 0.5: far 29 (30 s run: 35; tabu with K=40 sampled moves: 121,
   much worse; dropped tabu).
4. Calibration, free involution family (f = 0, n = 168, the family that contains C168.1): equivariant SA from random,
   150 s, T 8 -> 0.5: far 106 (stalled after 46 s). So random-start search does NOT rebuild the n = 168 graph in this family.
5. Symmetric growth (grow.py): insert a new fixed pair (orbit insertion on a free edge orbit) into the symmetric far-46 graph
   at 170: n = 172 (f = 2) best 80 over 125 choices (histogram 80..100+). Same floor as c1's unsymmetric 80.
6. Depth-2 exhaustive plateau search (nb2, started 17:40Z): all 2-switch pairs whose first step keeps far 46 (about 62k
   evaluations per plateau node, 1108 plateau nodes at depth 1). At 20k of 62k first moves (17:43Z): best 46.

## 18:07Z update (coordinator message: foreground runs only, timeout 540 + Bash timeout 600000, stay active to 2 h)

7. Depth-2 plateau search (nb2) from the symmetric far-46 graph ended by its 540 s timeout at 50,000 of 62,000 first moves
   (830 plateau nodes expanded, about 51M depth-2 evaluations): best far 46, nothing lower. Not finished, but no hit.
8. Calibration rows logged to scoreboard (calib): Z2 fixed-edge family n=150 f=1 far 29; free Z2 family n=168 far 106.
9. Symmetric growth 170 -> 172 (grow.py, f = 2): best 80 (same as the unsymmetric c1 insertion value). Running equivariant SA
   from it (480 s, T 4 -> 0.4).
