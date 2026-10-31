# c3 NOTES (worker c3, squad handsoff-37, card c3: randomized exact Z_p lift search)

Start (UTC): 2026-10-31T15:44:58Z. Planned stop: about 2 hours later (about 17:44 UTC).

## Plan
- Build shared/prior/exact_jsearch.c, calibrate: p=7 k=12 D=7 (n=168) time to first solution, PROBE tree estimates.
- Write my own randomized solver (c3/rsolve.c): randomized DFS with restarts (Luby) and node limits, random value
  order, deepest-partial completion, lift + bin/score37 scoring.
- Then p=7 k=13 (n=182), p=5 k=17 (n=170), p=5 k=18 (n=180), p=7 k=14 (n=196).

## Log
- 15:45 jsearch (shared exact DFS, canonical order) p=7 k=12 D=7: 12.6M nodes in 5 min, NO solution (rate ~50k nodes/s).
  Known to exist: C168.1 has a free Z_7 action (|Aut| = 504, stabilizer order 3), so this is a calibration case.
- 15:50 wrote c3/rsolve.c: same tree and collision pruning as jsearch, children shuffled at every node, Luby restarts
  (budget0 * luby(i)), fresh seed per restart. Validated: exhaustive run gives the same node counts and solution
  counts as jsearch on (p,k,D) = (3,3,5) 118 sols/324 nodes, (3,4,5) 1412/4508, (5,3,5) 339/781, (3,5,5) 7905/45187.
  Every solution is lifted and checked by an in-process BFS (far must be 0).
- 15:55 rsolve p=7 k=12 D=7, budget0 = 1e5: 20 restarts (3.8M nodes, 70 s), no solution yet, maxne = 35 of 36 edges.
- c3/rsolve2.c = rsolve + child ordering by collisions added (env HEUR=1: least new collisions first with random ties;
  HEUR=2: plus noise). Validated on the same small cases (same counts).
- NOTE for Bash tool: foreground runs over 120 s get moved to background; always pass timeout (ms) to Bash.
- 16:02 rsolve2 (exact tree, shuffled children, Luby restarts) p=7 k=12: about 30M nodes over all runs, NO solution.
  The known solution exists (C168.1 quotient). Knuth probes (exact tree): 20k probes est 3.2e9 nodes, 400k probes
  est 2.4e11 nodes (rel. se 0.4), 0 solutions hit in any probe: the solution density in the canonical tree is far below
  1/400k, so random dives and random restarts cannot find it. HEUR=1 (order children by collisions added) gave no hit
  either (3.8M nodes, 360 s). NOPAR (no parallel base edges) probe is noise-dominated (est 2e16, rel se 0.95).
- 16:23 slack search p=5 k=17 (n=170, delta 42), SLACK=1 (allow one extra collision per vertex, lift far then counts the
  unreached pairs): 6.4M nodes in 300 s, zero complete bases; deepest partial 49 of 51 edges. Never reached a leaf.
- 16:29 SAT (pysat, cadical195): c3/sat_lift.py. Variables E[a,b,t] (base edge a-b with voltage t), degree 3 by
  cardinality encodings, walk-reachability layers R[j][(w,g)] from each of the 2k sources (u,0) with witness variables
  (walks need not be non-backtracking: a walk reduces to a non-backtracking one with the same endpoint), coverage of all
  same-side lift vertices by even walks <= 6. Validated: solutions for (3,4,5), (5,3,5), (3,5,5) verify with score37.
  p=7 k=12 D=7: 874k vars, 1.73M clauses, built in 5-7 s; cadical195 found NO solution in 500 s (16:29-16:37). With
  symmetry breaking (SYM=1: N(base 0) = {0,1,2}, voltages at base 0 zero, valid gauge): NO solution in 500 s (16:38-16:46).
