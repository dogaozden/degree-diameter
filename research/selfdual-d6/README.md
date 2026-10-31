# selfdual-d6: self-dual (bipartite Cayley) Haar graphs at diameter 6

Job "selfdual-d6" (Opus cloud session, Oct 31 2026, from 08:30 UTC). Method of `../selfdual-d5/README.md` and
`../d75-raise/README.md` taken to D = 6, in the cells where no generalized hexagon exists (Delta - 1 not a prime
power). Targets (ours, from Delorme's hexagon doubling and our Theorem D; table in parentheses): (7,6) 9,592 (8,992),
(11,6) 148,944 (142,464), (13,6) 388,972, (15,6) 870,440, (16,6) 940,846.

(Status: in progress; this file is rewritten at the end of the job.)

## The test at diameter 6

H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S, |S| = K. Right multiplication by G is transitive on each
side. From (e,A), side B within distance 1, 3, 5 is S, S S^-1 S, S S^-1 S S^-1 S. So

  diam H(G,S) <= 6  iff  S S^-1 S S^-1 S = G,

and this one condition already gives the same-side conditions ((S^-1 S)^3 = S^-1 (S S^-1 S S^-1 S), (S S^-1)^3 =
(S S^-1 S S^-1 S) S^-1). This is the D = 6 form of the side-A test of selfdual-d5 (there: X X = G, X = S^-1 S, at
distance 4; here: the cross test at distance 5). Unlike D = 5, self-duality does not remove a condition at D = 6.
What it does: if psi(S) = S for psi(x) = u0 beta(x)^-1, then psi(S S^-1 S S^-1 S) = S S^-1 S S^-1 S, so the
uncovered elements come in psi-pairs, and the graph is a bipartite Cayley graph (vertex-transitive).

## Tools (src/)

`sdhi.c`, `haar_sd.c`, `build_sdhi.py`, `meta_list.py`, `sweep.py`, `hsd_queue.py` are copied unchanged from the
selfdual-hi job (branch claude/selfdual-haar-d7-d8-rwwjp8, `research/selfdual-hi/src/`), which already wrote them for
any D: at even D = 2k the energy is the number of side-B elements outside S X^(k-1), X = S^-1 S, i.e. the test above.
Read their header comments. `count_model.py` (new): the counting model of `../frontier/SIZE_LAW.md` at D = 6.
`apsp` = research/lifts/coordinator_check/apsp.c.
