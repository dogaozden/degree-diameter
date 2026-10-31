# sd5-r1 cards (goal (6,5) > 684; rules COMMON.md)

c1 order-4 self-duality: psi(x) = beta(x)^-1 with beta of ORDER 4 in Aut(G) (psi then has order 4; S a union of
   psi-orbits still gives a colour-swapping automorphism, so X X = G is enough, but the graph need not be Cayley).
   K = 6 types: {e} + 1 psi-fixed + one 4-orbit; one 2-orbit + one 4-orbit; {e} + one psi-fixed... (list them). Use
   d75 export.g (ALPHA 4 records) and adapt haar75.c run_anti4 to valency 6. Groups of order 361-420 with <= 7
   involutions (list via research/selfdual-d5/src/list_groups.g), smallest orders first.
c2 tabu inside the self-dual family (adapt d75-r2/c4/anneal.c to K = 6): the types sdk only samples (many psi-fixed
   elements: (4,1), (6,0)); calibrate on SL(2,7) (336,114) and on SmallGroup(352,50) (best 1), then groups of order
   361-400 with many involutions (the sweep log research/selfdual-d5/logs/K6/sweep.txt shows which had SAMPLED types).
c3 plain (not self-dual) Haar sets, tabu or annealing on general S (|S| = 6, e in S), cost |G \ XX| + |G \ YY|, fast
   incremental cost; calibrate on SL(2,7) first (must reach cost 0); then non-solvable or perfect-ish groups of order
   361-420 (e.g. SmallGroup(420, *), SL(2,5)-extensions) and the near-miss groups of the sweep.
c4 bi-coset graphs B(G; H, K; D), |H| = |K| = 2, valency 6 (|D| = 3 double cosets of size 2 or ... design it), on
   |G| vertices: groups of order 690-760, self-dual variant (d75-r2/c1/bsd75.c) or exhaustive (bic75.c logic).
c5 regular lifts of a 6-regular bipartite base graph on 2+2 or 3+3 vertices (multigraph with parallel edges) with
   voltages in a group Gamma: 4|Gamma| or 6|Gamma| > 684; adapt d75-r2/c2/sym22.c or lift22.c (valency parameter);
   metacyclic Gamma of order 172-200 (2+2) or 115-130 (3+3); calibrate on a known small case first.
c6 automorphism-invariant (not self-dual) Haar sets: S invariant under alpha in Aut(G) of order 3 (two 3-orbits, or
   3 fixed + one 3-orbit) or order 5 (1 fixed + one 5-orbit), check both X X and Y Y; adapt haar75.c exh to K = 6;
   groups of order 361-400.
c7 wildcard: find an approach none of c1-c6 uses (c1 order-4 self-dual Haar, c2 self-dual tabu, c3 plain tabu, c4
   bi-coset, c5 base-graph lifts, c6 order-3/5 symmetric Haar). Ideas: Cayley graphs of order 2n groups that are not
   Haar-type, non-Cayley vertex-transitive graphs from coset graphs, generalised polygon pieces, product/graph
   operations on the 672 graph, ... Pick ONE, make it concrete, run it.
c8 wildcard: same list as c7; choose something different from what c7 is likely to pick (e.g. algebraic: incidence
   structures over finite fields of size ~350-380 per side; or explicit families C_p : C_k with formula-only search at
   orders 361-600, beyond the director's SmallGroups range).
