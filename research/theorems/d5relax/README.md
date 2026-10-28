# d5relax: relaxed sets without the spread condition (job d5-relax)

Follow-up to research/theorems/D5_QUADRANGLE.md (§7, Lemma 7.3) after point 6 of the referee report
research/referee/d5-quadrangle.md: in the layout HHHDHHD partner pairs of a relaxed set may meet at ovoid points, so the
searches for relaxed sets of W(q) no longer need the condition "no pair on a line of the regular spread".

| file | what it does |
|---|---|
| export_w.py | writes data/W<q>_adj.txt (collinearity graph), _lines.txt, _spread.txt (regular spread of Lemma 1.1) with gqlib's numbering |
| export_q4.py | data/Q<q>_adj.txt, the collinearity graph of Q(4,q) (relaxed point sets, the dual question) |
| rtabu.c | fixed-size tabu search for relaxed sets of any graph; `-S spread` adds the old spread condition |
| exact_mip.py | exact maximum relaxed set by MIP (HiGHS), with or without the spread condition (solves q = 3; q = 5 too slow) |
| orbits.py | relaxed sets as unions of orbits of subgroups of Sp(4,q), exact MIP over the orbit matrix; class WSp (coordinates, transvections) |
| c61.py | the cyclic subgroups of order (q^2+1)/2: no orbit is relaxed (q = 11) |
| score.py | independent scorer (collinearity recomputed from coordinates) |
| analyze.py | structure of a relaxed set: pairs, pairs on spread lines, lines met |
| ceilings.py | largest order the construction can give per cell (Delta, 5), from the slot formulas and the counting bound |
| build_zo.py | builds the seven-level graph with the hub assignment of Lemma 7.3 (pairs may meet at ovoid points); `BREAK=1` breaks the rule for one such pair |
| graphs/ | solution files, edge lists, all-pairs checks |

Graphs (checked with research/lifts/coordinator_check/apsp_mt.c; rebuilt independently by research/theorems/d5gq/sol2edges.py
and research/referee/d5_checks/rebuild_record.py, both with identical edge sets):

- graphs/d15D5type_q11_zo89.*: (15,5)-type graph on 20,715 vertices over Q(4,11), relaxed set of 89 lines
  (graphs/W11_relaxed_set_89.txt, points of W(11)) with 36 pairs, 4 of them meeting at ovoid points; VALID, degree 12-15,
  diameter 5. Not a record (lab 20,736).
- graphs/neg_q11_zo89_break.*: the same with the level-3 slot of one hub of a pair meeting at an ovoid point moved off the
  partner: diameter 6.

Rebuild: `python3 export_w.py 11 && python3 build_zo.py 11 graphs/W11_relaxed_set_89.txt OUT 1` then
`cc -O3 -pthread -o apsp_mt ../../lifts/coordinator_check/apsp_mt.c && ./apsp_mt OUT.edges 15 5 4`.
