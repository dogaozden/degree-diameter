# d5gq: tools for research/theorems/D5_QUADRANGLE.md (job thm-gq-d5)

Bipartite graphs of diameter 5 from generalized quadrangles: level graphs, surgery, hubs.

| file | what it does |
|---|---|
| gqlib.py | W(q), Q(4,q) = W(q)^D, Q(5,q), H(3,q^2), AS(q) (Payne derivative); regular spread of W(q) (Lemma 1.1) |
| levels.py | level graph + freed sets + hubs (Definitions 2.1, 3.1) as an edge list; arbitrary regular tournaments |
| repair.py | Theorem E test (`exact_conditions`) and the two-level brute force (`brute_bad`) |
| test_basic.py | Theorem A on 32 random level graphs; Theorem E = brute force; Theorem B (output test_basic_out.txt) |
| triads.py | triad centre counts in W(q), Q(4,q) (triads_out.txt) |
| localdual.py | two-point local dualities (Proposition 6.4) |
| layouts.py | best typings of regular tournaments (Section 8) |
| hubopt.py | hub graph search for (HG) (same-colour hubs within distance 4, level paths counted) |
| build_typed.py | typed rotational layouts over Q(4,q) with ovoid / partial ovoid / local dualities + hubs |
| build_relaxed.py | the same with relaxed line sets on D->H arcs and the hub rule (Proposition 7.2) |
| wgr.py, wgr_eval.c | whole-graph annealer (Section 12): extra freed points on non-friendly arcs, bad pairs counted on the whole graph |
| relaxed.c, mk_relaxed.py | annealing for relaxed sets of W(q) |
| check_rule.py | checks the hypotheses of Proposition 7.2 in a solution file |
| sol2edges.py | independent rebuild of a graph from its solution file (re-checks W(q) from the listed coordinates) |
| family_table.py | values of the explicit families (Corollaries 10.1-10.4) per cell (family_table_out.txt) |
| graphs/ | solution files, edge lists and all-pairs check logs; the (13,5) record is d13D5_q9_relaxed66_n11636.* |

All-pairs check: `cc -O3 -o apsp ../../lifts/coordinator_check/apsp.c && ./apsp <(zcat graphs/d13D5_q9_relaxed66_n11636.edges.gz) 13 5`.
