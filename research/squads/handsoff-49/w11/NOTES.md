# w11 NOTES: exhaustive certification of the best metacyclic Haar graphs

Start: 23:13 UTC. Planned end: 01:15 UTC (2 hours). Card: cards.md, "## w11".

## What the code does (exh.c, compiled to ./exh)
- Haar graph H(G,S), |S| = 4, G = Z_m x|_r Z_k, N = mk, n = 2N. Edges (g,A) ~ (s g,B), s in S.
- Normalisation (exact): H(G,S) = H(G, d S c^-1), so S can contain e; and H(G,S) = H(G,sigma S) for sigma in Aut(G).
- Automorphisms used: AUT = all verified maps (a,j) -> (u a + c S_j, j), u a unit, S_j = sum_{i<j} r^i. Each map is
  checked as a homomorphism on the generators (1,0), (0,1) (this suffices). Orbits of AUT on G\{e} give the
  representatives x of S = {e,x,y,z}. For each x, the stabiliser of x in AUT acts on unordered pairs {y,z}; only the
  least pair of each orbit is evaluated (canonical check, exact).
- Cost = haar_gen3 convention (D = 9 odd): for each root (e,A), (e,B): number of vertices on the root's own side not
  within D-1 = 8 steps. Cost 0 iff diameter <= 9. Early exit when the running cost exceeds the bound.
- The bound starts at the screen cost cs (w2's haar_tab cost) and only goes down, so the printed minimum is exact.

## Checks
- Calibration meta 71 35 49 (N = 2485, the valid 4,970 table graph): exh finds cost 0 (24 hits), written
  out/cal71_c0.edges; apsp: RESULT VALID d=4 D=9 n=4970, INVALID at D=8. So the cost and the symmetry reduction work.
- Matches earlier exhaustive results: m101_k25_r5 (2,525) minimum 2; m104_k24_r7 (2,496) minimum 4.

## Driver
- `run_list.sh LIST BUDGET`: lines "m k r cs"; runs exh per group (resumable state in state/, hits in hits/), writes
  certified.tsv and scoreboard lines; a cost-0 hit is checked with apsp and copied to ../records/w11_n<n>.edges.
- Lists: list_meta_c12.txt (26 groups, w2 screen cost <= 12; list_run1.txt is the same file).

## Results (certified.tsv has the full table)
- m101_k25_r5 N=2525 min 2 (25 reps, 14 s)
- m104_k24_r7 N=2496 min 4 (67 reps, 34 s)
- m208_k12_r3 N=2496 min 4 (51 reps, 23 s)  <- new: w2 had only the screen value 4 for it
- Groups are ~15-60 s each now, so the whole cost <= 12 list takes about 15 min.

## Next
- Extend to all metacyclic groups of order 2,486..2,600 in screen-cost order (cs <= 20, then more), keep the table.
- Idea not yet tried: full Aut(G) (more automorphisms, smaller orbit set), and the non-split groups in w2's nsA.tsv
  (tables, need their automorphisms from a generator-based search).

## Update 23:25
- exh3.c (binary exh3): pairs {y,z} are scanned in lex order and marked with a visit stamp; each unmarked pair is
  searched and marks its stabiliser images, so the work is one BFS per pair orbit (faster than the canonical test in
  exh.c). Also takes table groups ("tab FILE"): automorphisms = inner automorphisms, so non-split groups from w2's
  nonsplit.py work too (tables in tabs/). Calibration of exh3 still to be run before switching the driver to it.
- run_any.sh LIST BUDGET [BIN]: lines "meta m k r cs" or "ns m k r s cs"; resumable; records certified.tsv and scoreboard.
- Lists: list_run1.txt (26 split groups, cs <= 12), list_run2.txt (79 split groups, cs 13..40), list_ns_c20.txt
  (51 non-split groups, cs <= 20).
