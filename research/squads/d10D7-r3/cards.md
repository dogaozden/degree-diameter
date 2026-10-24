# Round 3 cards (Opus, 2026-10-24 ~22:50 UTC). Common brief: README.md in this folder.

c1 EXACT JOINT COVERS FROM STRUCTURE (light, Python). Find K >= 4 pairwise opposite flags of H(8) with membership-vector
   mismatch 0 (or as small as possible). Random opposite flags give 0 at K = 3 but 12-226 at K = 4 and ~3,000 at K = 12.
   Try structured families: flags of the subhexagon H(2) (points whose 7 coordinates lie in GF(2); hex_q8.bin stores
   N*7 uint8 coordinates after the line table, GF(8) element = a0 + 2 a1 + 4 a2), unions of orbits of the Frobenius
   x -> x^2 (coordinate-wise), flags sharing a common opposite flag, flags in one apartment-like configuration, etc.
   Score: largest K with mismatch 0 (metric "maxK_mismatch0"); also report mismatch at K = 8 and 12 for your best family.
c2 FLAG-SET LOCAL SEARCH (light-medium, Python). Minimise mismatch at K = 16 (random opposite flags give ~5,000-6,000)
   by local search over the flag set (replace one flag by a better opposite candidate, annealing, best-of-many
   greedy). Score: mismatch at K = 16 (lower is better); also K = 24 if time.
c3 LEFTOVER MATCHING (light, Python). For 21 random opposite flags (seed 1) joint_cover() matches equal vectors and
   zips the leftovers. Find a better leftover assignment (min Hamming distance, min-cost matching per class, greedy
   swaps judged by hexkit.uncovered) that minimises the total uncovered targets (sum over pairs and both sides).
   Score: total uncovered at K = 21 (report the baseline too). Give code d7hex could adopt.
c4 SPIN-OFF AND TUNING AT q = 5, cell (7,7) (our record 23,488 = K 26). Use d7hex alg 4 + OPPFLAGS (+ GROW) on
   hex_q5.bin; hub degree cap is q-1 = 4, so start hub graphs with degree 2-3 and HGDEG <= 3. Find settings that solve
   the largest K. Score: largest K with apsp VALID (metric "K_valid_q5"; vertices 23,436 + 2K). Beat 26 if you can.
c5 SPIN-OFF AND TUNING AT q = 7, cell (9,7) (record 117,690 = K 21). Same as c4 on hex_q7.bin (hub cap 6). One run at
   a time (each uses a core). Score: largest K with apsp VALID at q = 7 (vertices 117,648 + 2K).
c6 PROXY EXTENSION (C). In a copy of d7hex.c in your folder, add two route types to the proxy: side A (−,−):
   (p,0) -> line L through p -> (M^-1(L), level 2) -> line L' through it -> (M^-1(L'), level 1) -> point within
   distance 2; side B (+,+) dually ((l,0) -> point y on l -> (M(y), 1) -> point y' on it -> (M(y'), 2) -> line within 2).
   Both are real routes of length 6 that the proxy ignores today. Measure at q = 5 whether the largest solvable K
   grows (same seeds and time, with vs without). Score: largest K solved at q = 5 with apsp VALID using your binary.
c7 WILDCARD: MORE THAN HUBS (q = 5 testbed). Find a different local modification of X(M) that adds vertices more
   cheaply than +2 per freed pair (e.g. new vertices on 3 different freed points at 3 levels, hubs sharing freed
   edges, partial freeing, rewiring a few hexagon edges, vertices attached to hubs). Other cards: c1-c3 joint-cover
   structure, c4-c5 hub tuning, c6 proxy routes, c8 new constructions. Score: vertices over 23,436 at q = 5 with
   apsp VALID (and how many extra edges/freed pairs it cost).
c8 WILDCARD: A DIFFERENT CONSTRUCTION. Anything that is not hubs on X(M): a different base, a lift with a cleverer
   voltage group, gluing two structures, using the 2·|H(8)| spare... It must be checked by apsp (a real graph), at
   (10,7) or as a scaled analogue that beats 3·|H(q)| + hubs at q = 2, 3, 4, 5 with Δ = q + 2, D = 7. Other cards as
   listed in c7. Score: vertices with apsp VALID and the cell.
