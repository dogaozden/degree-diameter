# Squad d5relax-r1: large relaxed sets of W(11) (job d5-relax)

## The problem (read this first)

W(q) is the symplectic generalized quadrangle: points = the (q+1)(q^2+1) points of PG(3,q); two points x, y are
*collinear* iff w(x,y) = x0*y2 + x1*y3 - x2*y0 - x3*y1 = 0 (mod q). Lines are the totally isotropic lines; every point is
on q+1 lines, every line has q+1 points, every point is collinear with q(q+1) others.

A **relaxed set** T is a set of points in which every point of T is collinear with **at most one** other point of T
(the collinearity graph induced on T is a matching plus isolated points). Pairs may lie on any line. (An older search
also forbade pairs on the lines of a fixed regular spread; that condition is dropped now, which is the point of this
job.)

**Goal: a relaxed set of W(11) with at least 111 points** (1464 points, collinearity degree 132). That would give a
bipartite graph of degree 15, diameter 5 above the lab's 20,736 vertices. Best known so far: 89 (tabu search, this
job), 88 with the old spread condition. Counting bound: 127 (each point uses q+1 lines, a pair uses 2q+1). Smaller
cases for calibration: q = 5 (156 points): 23 found; q = 7 (400 points): 41; q = 9 (820 points): 66.

## Tools (all in research/theorems/d5relax/)

- `data/W<q>_adj.txt`: n, then per point "degree neighbours..." (collinearity graph), q = 3,5,7,9,11,13.
  `data/W<q>_lines.txt`: the lines (q+1 points each). `data/W<q>_spread.txt`: spread line index per point.
- `rtabu.c` (binary `./rtabu`): fixed-size tabu search. `./rtabu data/W11_adj.txt SECONDS SEED OUT [-i START] [-k K]`.
  Output file format: first line = size, then one point per line.
- `orbits.py`: class `WSp(q)` with point coordinates `P` (n x 4 array), collinearity matrix `C`, symplectic
  transvections and random elements of Sp(4,q) as point permutations; `best_union` finds the best union of orbits by MIP
  (HiGHS, `import highspy`). `python3 orbits.py q n_elements seed`.
- `analyze.py q FILE`: structure (pairs, pairs on spread lines, ...).
- Python has numpy, highspy (MIP), python-sat (pysat, SAT solvers incl. cadical).

## Scorer (the only thing that counts)

    python3 research/theorems/d5relax/score.py 11 YOURFILE

prints `{"q": 11, "size": ..., "pairs": ..., "valid": true}`. FILE: rtabu format or a JSON list of point indices
(the numbering of data/W11_adj.txt = orbits.WSp(11)).

## Machine rules

4 cores and 15 GB shared with the director and 7 other cards: single-threaded only, `timeout 900 nice -n 10 <cmd>` for
anything heavy (at most 15 minutes per run, about 25 minutes in total), at most 1.5 GB of memory, no git commands, no
edits outside your card folder `research/squads/d5relax-r1/<card>/`. Compile C with `gcc -O3 -march=native`.

## Report

Append ONE line of JSON to `research/squads/d5relax-r1/scoreboard.jsonl`:
`{"card": "c5", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <best size>, "valid": true|false,
"next": "<one line>"}` — score = the size printed by score.py on your best file (save it as `best.txt` or `best.json`
in your folder). Then reply in at most 5 lines.
