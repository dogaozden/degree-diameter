# Squad round d14D7-r5 (job cell-14-7, third session): bigger pairwise-opposite point sets of H(11)

## Goal
Find a set R of **at least 757 points of Q(6,11) that are pairwise non-orthogonal** (equivalently pairwise opposite
points of the split Cayley hexagon H(11), a partial ovoid of Q(6,11)). The best known has 756 (squad r4 c1 of the
cell-13-7 session). The (14,7) record on master is 1,774,584 = 5·354,312 + 4·|R| with |R| = 756, so every extra point is
+4 vertices at (14,7) (+2 at (13,7), +6 at (15,7)). Upper bound q^3+1 = 1332 (not attained: no ovoid for q = 11).

Points: x in F_11^7, x != 0, Q(x) = x0*x4 + x1*x5 + x2*x6 - x3^2 = 0 (177,156 projective points).
Bilinear form B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 (mod 11). R is valid iff B(x,y) != 0 for all x != y in R.

## What is known (do not repeat)
- Plain local search on the 177k-point graph stalls at about 400. Big sets come from SYMMETRY: R = union of orbits of a
  group G of isometries, chosen by a maximum-weight clique on the "orbit graph" (good orbits = internally pairwise
  non-orthogonal; two orbits adjacent iff all their cross pairs are non-orthogonal).
- 756 = orbits of a cyclic group of order 15: rotation of order 3 on an elliptic (anisotropic) plane A, scalings
  diag(z, 1/z) and diag(z^2, 1/z^2) (z of order 5) on two hyperbolic planes, identity on the last vector.
  Generator: research/cell147/ovoid/g15.txt. 720 from abelian groups of orders 25 and 75 on the same kind of blocks.
- Opus is sweeping all cyclic subgroups (orders 6-80) of the ten maximal tori of SO(7,11) right now. Do not do that.
  Your card is a DIFFERENT group family or idea.

## Tools (research/cell147/ovoid/; build once: `gcc -O3 -march=native -o orbclq orbclq.c -lm` is already done)
- `orbclq GENS -t SECONDS -s SEED -o OUT.txt [-w WARM.txt] [-x EXACTK] [-v]`: reads generator matrices (7x7 integers,
  row-major, acting on COLUMN vectors x -> M x, '#' comments, any number of generators), computes orbits, good orbits,
  the orbit graph and a max-weight clique (strong tabu search; exact branch and bound when K <= EXACTK, default 400).
  stderr: orbit-size histogram "size:count/good", K, graph density. stdout: `RESULT ... good=K ... best=N ...
  pairs_orthogonal=0`. OUT.txt = the point set (7 coordinates per line). It refuses matrices that do not preserve Q.
  Speed: K=8000 builds in 3 s, tabu ~100k iterations/s; K=30000 builds in ~20 s, memory K^2/8 bytes.
  The tabu finds the 756 set of g15.txt from scratch in 1-10 s. For K < ~3000 runs of 20-30 s are plenty.
- `ovlib.py` (python3, no numpy needed): `torus(types)` (explicit maximal tori, e.g. ['E','H','H','L'],
  ['E6','L'], ['H4','E','L'] - see its docstring), `elem(gens, exps)`, `invariant_forms(mats)` (symmetric forms
  preserved by a group), `conjugate_to_standard(mats, gram)` (moves a group preserving the form `gram` to the
  standard form; use it whenever you build a group in other coordinates), `random_isometry()`, `mat_mul`, `mat_inv`,
  `mat_pow`, `mat_order`, `is_isometry(M, std_gram(11), 11)`, `group_order(mats)` (closure, small groups),
  `write_gens(path, mats, comment)`, `read_gens(path)`.
- `checkset.py FILE` independent check of a point file -> `RESULT VALID n=...`.

## Scorer
`python3 research/cell147/ovoid/checkset.py YOUR_SET.txt` must print `RESULT VALID n=N`; your score is N.

## Rules (shared machine: 4 cores, 15 GB, Opus and 8 cards)
- Single thread. Wrap every heavy run: `timeout 900 nice -n 10 ...`; keep orbclq runs to `-t 60` or less unless
  a run is clearly promising; at most ONE heavy process at a time; <= 1.5 GB memory (K <= 40000).
- Work ONLY in your folder research/squads/d14D7-r5/<card>/ (copy tools there or call them by path). No git.
- Time box: about 40 minutes of work.
- At the end append ONE JSON line to research/squads/d14D7-r5/scoreboard.jsonl:
  {"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command for the best>", "score": N,
   "valid": true|false, "file": "<best set path>", "next": "<one line: what to try next>"}
  and reply to Opus in at most 5 lines (best score, group, file, one insight).
