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

## Update 00:43 (coordinator instructions applied)
- Foreground only now (run_any.sh, timeout 530 nice -n 10). No background jobs.
- exh3 (orbit-marking, table groups via inner automorphisms) calibrated: meta 71 35 49 min 0 (valid 4,970 graph,
  apsp VALID at 9), 101 25 5 min 2, 104 24 7 min 4; evaluation counts identical to exh.
- Scoreboard: 13 of my earlier lines (the first driver version appended every result) are NOT a new lowest cost at
  their n and are still in scoreboard.tsv; the coordinator should remove the lines whose worker column is w11 and
  whose time is before 23:30. (I was not allowed to remove them myself: the safety check blocked the rm command.)
  run_any.sh now appends only for a new lowest cost at its n.
- Certified this session (certified.tsv has all rows): split groups in list_run1 done up to m208_k12_r11; the remaining
  split groups of list_main were done (m105_k24_r52 12, m320_k8_r7 12, m427_k6_r13 12, m416_k6_r367 12, m52_k48_r7 12,
  m215_k12_r92 10, m208_k12_r115 10 (screen 11; exhaustive 10), m208_k12_r69 12).
- Non-split (ns) groups: slow (inner automorphisms only, 80-270 reps, 2-14 min each); 22 still open at 00:43
  (state files resume them).
- Not yet: 2,601..2,700 screen (haar_tab 2 s) and certification at cost <= 8.

## Update 01:06
- 2,601..2,700: enumerated 1,583 metacyclic groups (groups_2601_2700.txt). Screened 281 of the 777 with k >= 4 and
  |G/G'| <= 200 (screen2601.tsv, haar_tab 4 9 1.5 s, seed 1). Best screen cost 10 (2604 434 6 5, 2653 379 7 86,
  2667 127 21 25). None at cost <= 8, so nothing to certify from this subset. The other 496 of the 777 and the k <= 3
  groups are not screened yet.
- Non-split groups still open at 01:06 (state/ files resume them): ns_m420_k6_r109_s35 (paused at rep 144),
  ns_m208_k12_r29_s52, ns_m208_k12_r37_s52, ns_m208_k12_r43_s104, ns_m208_k12_r11_s104, ns_m52_k48_r7_s26,
  ns_m104_k24_r7_s52, ns_m104_k24_r11_s52, ns_m104_k24_r37_s26, ns_m70_k36_r3_s35, ns_m105_k24_r52_s35,
  ns_m210_k12_r23_s105, ns_m210_k12_r73_s35, ns_m208_k12_r115_s104, ns_m208_k12_r7_s104, ns_m208_k12_r69_s52,
  ns_m416_k6_r367_s208, ns_m70_k36_r23_s35, ns_m105_k24_r37_s35, ns_m210_k12_r37_s35, ns_m320_k8_r7_s160.
- Resume: cd w11 && timeout 530 nice -n 10 ./run_any.sh list_metafirst.txt 450 ./exh3 (foreground).
- Records: no cost 0 found anywhere (no record). Best new exact minima: m208_k12_r115 (2,496 split: m208 k12 r115 is
  split, 2,496 cost 10 from screen 11), m215_k12_r92 (2,580) cost 10.
- Next idea: per-pair search with the full Aut(G) for the non-split groups (inner automorphisms are too few; the
  slow ns groups take 10-15 min each), then the 496 unscreened k >= 4 groups of 2,601..2,700.
