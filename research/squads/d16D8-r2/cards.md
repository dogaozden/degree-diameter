# d16D8 round 2 cards (Opus, 2026-10-25): W(q) testbed, Z_m lifts of I + 2 matchings at diameter 6

c1 Annealing frontier: push plain baselift annealing as far as it goes (moves, temperatures, restarts, longer runs,
   starting from the best smaller-m design and adding sheets); largest VALID m at q = 5, 7, 11 (and 13 if feasible), so we
   have the unstructured scaling curve to compare the structured cards against.
c2 Z_5 x Z_k level skeleton (the D=5 polygon cover with k sheets): voltages in Z_5k (k coprime to 5), flags = 0 mod 5,
   matching 1 = 1 mod 5, matching 2 = 2 mod 5; anneal only the sheet parts (FIXMOD=5). Largest k at q = 7, 11, 13
   (DGQ analog: k = 6, 8, 9).
c3 Algebraic voltages from coordinates of W(q): flag voltage from the position of the point on its line (a PG(1,q)
   parameter), discrete logs, coordinate ratios; matchings from linear maps (P -> line <P, A P> for B(P,AP) = 0) or
   random; groups Z_(q-1), Z_q, Z_(q+1), Z_2(q+1), ... Find any algebraic family that is VALID at larger m than random.
c4 Symmetric designs: a cyclic group C of collineations of W(q) acting semiregularly (no fixed points or lines), voltages
   constant on C-orbits, matchings C-equivariant; anneal orbit parameters. Does symmetry let annealing go higher at
   q = 7, 11, 13?
c5 Other level skeletons: levels Z_L, matchings move the level by t1, t2 (flags by 0), k sheets on top (FIXMOD=L):
   scan (L, {t1,t2}) such as (5,{1,2}), (6,{1,2}), (7,{1,3}), (8,{1,3}), (10,{1,4}), (11,...); report max L*k at q=7, 11.
c6 Rainbow hypothesis: for odd q the DGQ count is m = 5k with q+3 = 2(k-1). Take a proper (q+3)-edge-colouring of
   I + M1 + M2 (a 1-factorization of I plus the two matchings), voltage of each edge = f(colour) with f mapping the q+3
   colours 2-to-1 onto Z_k \ {0}, plus a Z_5 skeleton (m = 5k). Test VALID at q = 7 (k=6), 11 (k=8), 13 (k=9);
   anneal f / Kempe-swap the colouring.
c7 Targeted repair search: repeatedly take an uncovered (source, target, sheet), change one edge voltage on a short
   walk so that it gets covered, accept if the all-source count does not increase (or Metropolis); q = 7, then 11.
c8 Wildcard: an approach none of c1-c7 uses (structured matchings such as M2 = M1 composed with a collineation,
   matchings from a polarity-like map, voltages that are a potential plus a twist, copies of W(q) and its dual Q(4,q),
   a non-cyclic group with your own checker, ...).
