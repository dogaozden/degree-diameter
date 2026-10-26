# Shared files for squad round table-audit-2-r1 (read-only for cards; copy what you change into your own folder)

Problem: Gomez's compound graph Omega H(q) (thesis 1986, Fig. 2.21): 5*alpha copies of the generalized-hexagon
incidence graph H(q) plus 10n hubs; every copy marks one point and one line per row t (n rows); hubs (t,k), (t,kbar)
attach to the marked vertices of row t in the copies the figure says.  The thesis's own labelling (same row = same
label in every copy) has diameter 9.  With a free labelling of every copy, q = 3 reaches diameter 8 (found today).
Goal: diameter 8 at q = 5 (alpha = 4, 195,300 vertices) and q = 4 (alpha = 3, 54,600 vertices), then q = 7.

- hQ.txt: H(q) edge list (first line = vertex count; points 0..n-1, lines n..2n-1).  n = 364, 1365, 3906, 19608.
- gQ.txt: one automorphism g of H(q) (a permutation of 0..2n-1) acting semiregularly: order 13 (q=3), 7 (q=4),
  31 (q=5), 19 (q=7).
- omega_model.h: the construction for an arbitrary labelling (read its header comment).
- omega_symanneal.c: simulated annealing over G-equivariant labellings (G = <g>), with the Z5 twist (ZMODE=2).
  `ZMODE=2 HUBONLY=1 ./omega_symanneal hQ.txt gQ.txt TYPES INNER 8 SECONDS SEED OUTPREFIX` prints the best cost and
  writes OUTPREFIX.lab.  Cost = number of (source, vertex) pairs at distance > 8 from the hub orbit representatives;
  cost 0 means the hubs reach everything (the final line also prints the check over all orbit representatives).
- omega_eval: `./omega_eval hQ.txt TYPES INNER LAB 8 all` (exact, all sources, no symmetry; slow above q = 4) or
  `... hubs` / `... hubs0`.  omega_profile: where the far pairs are.  apsp: independent all-pairs checker
  (`./apsp EDGES d 8`).  omega_verify.py: independent wiring check.
- Baselines (lead, 4 cores shared): q=5 abab LLLL ZMODE=2 HUBONLY: random start 42,280, 35,867 after 325 s
  (5,357 iterations); q=4 aba LLL: 13,103 after 327 s (16,623 iterations).  q=3 aba LLL: 0 after 70 s.
