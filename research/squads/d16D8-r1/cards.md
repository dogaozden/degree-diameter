# d16D8 round 1 cards (Opus, 2026-10-24)

c1 X(M) skeleton: G = Z_5 x Z_k; jump 1 always moves the Z_5 coordinate by +1, jump 2 by +2, flags by 0 (the D=7
   construction of the table); anneal only the Z_k parts (MOVES=wtM). Largest k at q=3, 5.
c2 Incident jumps: M_1, M_2 two disjoint perfect matchings of H(q) itself (M_k(p) is a line through p), so every
   vertex has two doubled flags; anneal shifts with the matchings fixed (MOVES=vs) or swaps that keep incidence.
c3 Jump distance: bijections with d(p, M_k(p)) = 3 for all p, and separately = 5; compare with random bijections at
   the same annealing budget (q=3 and q=5).
c4 Edge-colouring flag shifts: a proper (q+1)-edge-colouring of H(q) (1-factorization); flag shift = f(colour)
   for a map f: colours -> Z_m; jumps random or equal to two colour classes; anneal jump shifts and f.
c5 Plain annealing push: best effort with the existing annealer at q=5 (m = 18, 20, 22, 25): temperatures,
   sampled vs all sources, restarts; how high can unstructured search go in 25 minutes?
c6 Line-local projective coordinates: each line is a 2-space; its points get an index 0..q from a canonical basis
   (reduced row echelon form); flag shift = function of that index (and/or of the point's index on other lines);
   jumps random, annealed.
c7 Group choice: same budget, different G of the same order m: Z_m, Z_2 x Z_(m/2), Z_k x Z_k, Z_3 x Z_(m/3);
   which group gives the largest VALID m at q=3 and q=5?
c8 Wildcard: an approach none of c1-c7 uses (for example level-dependent structure inside the lift model, jumps
   chosen by a geometric rule such as M(p) = a fixed line at distance 5 found by coordinates, combining a DGQ-like
   skeleton with annealing, or something else entirely).
