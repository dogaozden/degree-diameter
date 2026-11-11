# Referee checks for D5_QUADRANGLE.md (job referee-d5)

Programs written for research/referee/d5-quadrangle.md. They share no code with research/theorems/d5gq/. The writer's
files are used only as input data (solution files, the card c4 example, whose Q(4,5) labelling comes from the writer's
gqlib and is validated here) and to compare edge lists after the rebuilds.

| file | what it does |
|---|---|
| gf.py | finite fields GF(p^k) as integer tables; projective points and lines |
| gq.py | W(q) from the symplectic form; Q(4,q) built directly from X0X1+X2^2+X3X4 = 0; GQ axiom check; the Klein map W(q)^D -> Q(4,q) |
| bfs.c | all-sources BFS (OpenMP): simple, bipartite, degrees, exact diameter, number of pairs beyond D (with `list`, the pairs) |
| rebuild_record.py | rebuilds a level graph with hubs from a solution file (Definitions 2.1, 3.1 only) and checks every hypothesis (Lemma 1.1 spread, relaxed set, Prop. 6.4, slots, hub rule, Y-degrees) |
| families.py, run_families.sh | the explicit graphs of Corollaries 10.1–10.4 from the printed ingredients, random choices where the note says "any"; a negative control |
| test_theorems.py, test_E_split.py | Theorem E, Theorem B, Prop. 6.4, Prop. 7.1, Prop. 7.2 against BFS in the two-level graph |
| check_c4.py | Computer-checked 6.5 (card c4's three-point set) |
| tourn.c, layouts_eval.py | all regular tournaments on 5, 7, 9 vertices with all typings; the optimum claims of §8 |
| nums.py | the numbers of §§0, 7–12, 14 (family values optimised over Lemma 9.1) |
| small_lemmas.py | Lemma 1.2(c) (all triads, q = 3, 5), Lemma 1.3, Lemma 1.4, the hub structure of the record |
| w5_ovoid.py, clique.c | largest partial ovoid of W(3), W(5) |
| arc36.py | report point 2: one more freed element on the arc 3->6 of the 11,636 graph, bad pairs in two levels vs. the whole graph |
| z_in_O.py | report point 6: a partner pair meeting at an ovoid point, both hubs at that point |
| run_all.sh | reruns everything; output in checks.log ($SCRATCH = a temporary directory) |

Rerun: `./run_all.sh <checkout of claude/gq-diameter-5-xa5d3d> <scratch dir> > checks.log` (about 6 minutes on 4 cores).
