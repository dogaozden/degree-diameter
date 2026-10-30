# Round s65r4 cards (goal: bipartite (6,5) graph on > 684 vertices)

Shared context: CONTEXT.md (see "New after round s65r3"). Evolved from s65r3: finish the exhaustive Haar search at
352-360 and open 361-380; use the new best local search (tabu) to repair the closest near misses in the full 2+2 lift
space, where the Haar and bi-Cayley symmetries no longer bind.

- **c1 Haar exhaustive**: resume 360_95 (pair 259), 360_100 (129), 352_169 (131); then 360_98, 360_28, 360_108.
- **c2 Haar exhaustive**: 352_56, 352_64, 352_84, 352_100, 352_139, 352_154.
- **c3 Haar exhaustive**: 352_163, 354_1, 360_23, 360_93, 360_103, 360_113, then 360_125, 360_136 (more involutions,
  annealing cost 4).
- **c4 Haar exhaustive, orders 361-380** (low-involution list research/s65/haar/next_361_380.txt), smallest |Aut| last.
- **c5 Haar near miss -> lift -> tabu**: the 12 side-A covers of 360_53 (lift cost 4, bad 360), tabu with several
  seeds each, kopt on the best.
- **c6 bi-Cayley near miss -> lift -> tabu**: bicay annealing on the untried bc files of order 352-360, then tabu in
  the full lift space from the best five.
- **c7 tabu from random starts at 704/720**: few-involution groups of order 176 and 180, three bases, kopt on finals.
- **c8 tabu on 3+3 lifts** (6|G| vertices, |G| = 116, 117, 120), bases from round 1's screen.
