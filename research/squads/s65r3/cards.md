# Round s65r3 cards (goal: bipartite (6,5) graph on > 684 vertices)

Shared context, scorer, rules: CONTEXT.md (sections "New after round s65r1/s65r2" at the end).
Evolved from s65r2: Haar graphs at 352-360 are the closest family (side A covered, side B 2 short), and exhaustive
haarex2 runs take minutes per group, so four cards finish the 63 open low-involution groups; the other four push lifts
(exact 2-opt pipeline, a better local search), bi-Cayley annealing, and Haar annealing over the never-run groups.

- **c1-c4 exhaustive Haar (haarex2)**, groups of research/s65/haar/list_r3_{0,1,2,3}.txt in order.
- **c5 lift pipeline at 704/720**: vl + exact 2-opt (kopt K=2) restarts over the few-involution groups of order
  176 and 180, three 2+2 bases.
- **c6 better lift local search**: tabu search / plateau moves over single-voltage changes with exact best-move
  selection; benchmark at 672 (order 168) against vl + kopt, then run at 704.
- **c7 bi-Cayley annealing sweep**: bicay MODE=sa over every bc group file of order 344-360, all (a, b).
- **c8 Haar annealing over the 260 never-run groups of order 352-360 with more than 3 involutions** (mcos 1|1).
