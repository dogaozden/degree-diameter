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

