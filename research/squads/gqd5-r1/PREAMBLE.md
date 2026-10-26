# Squad gqd5-r1 (job thm-gq-d5): common brief for every card

Repo /home/user/degree-diameter. Work ONLY in your folder research/squads/gqd5-r1/<card>/ (create it). No git commits, no
edits elsewhere. Machine: 4 cores shared by ~20 agents: single-threaded code only, wrap anything heavier than a few
seconds in `timeout 900 nice -n 10 ...`, stay under 1.5 GB of memory. Time box: about 20 minutes of real work.

Setting. Bipartite graphs of diameter 5 from 2r+1 copies ("levels") of the incidence graph I of a generalized quadrangle
(GQ) of order (q,q) (diameter 4, girth 8). Level j has a type H (colour A = points, B = lines) or D (A = lines, B =
points). For every level j and k = 1..r a bijection M_(j,k) from the A-elements of level j to the B-elements of level j+k
gives matching edges. Degree q+1+r, order (2r+1)*2(q+1)(q^2+1). A transition is friendly when the two types differ
(then M = identity is allowed). Surgery: delete the matching edges at a freed set R_t of A-elements; hub vertices take
one freed slot in every level (B-hubs at A-slots, A-hubs at B-slots) plus a bipartite hub graph Y of degree <= q-r.

Tools (Python 3 + numpy + python-sat; read the short docstrings first):
- research/theorems/d5gq/gqlib.py: W(q), Q4(q) (= dual of W(q)), Q5(q), H3(q), AS(q); GQ object: np, nl, lines,
  plines, col (point collinearity bool matrix), con (line concurrency), dpp/dll/dpl distances, I (incidence);
  regular_spread_W(G) (a spread of W(q) = an ovoid of Q(4,q)); is_partial_ovoid, is_partial_spread.
- research/theorems/d5gq/levels.py: build(G, types, M, R, Bhubs, Ahubs, Y) -> (n, edges); write_edges; apsp.
- research/theorems/d5gq/repair.py: brute_bad (two-level brute force), exact_conditions ((E1)-(E3) below).
- research/theorems/d5gq/layouts.py: best typings of regular tournaments.
- research/theorems/d5gq/apsp: all-pairs BFS checker. `./apsp EDGES d D` prints "RESULT VALID d=.. D=.. n=.." iff the
  graph is simple, bipartite, connected, max degree <= d and diameter <= D. This is the only accepted proof of validity.
  Edge file: first line n, then one "u v" per line.

Already established (do NOT redo; build on it):
1. Theorem A: any types, any bijections -> diameter <= 5 (checked q <= 5).
2. A friendly identity transition is repaired inside its two levels iff its freed set is a partial ovoid (pairwise
   non-collinear points) or partial spread (pairwise non-concurrent lines). The D = 7 "segment sets" do not carry over.
3. Theorem E (exact two-level criterion) for any transition M: A(level j) -> B(level j'), freed R:
   (E1) no A(j')-element has all its incident elements in M(R);
   (E2) for x in R, {M(a): a collinear/concurrent with x, a not in R} covers A(j') (each A(j') element incident with one);
   (E3) for x in R, {a not in R: M(a) at distance 2 from M(x)} covers B(j).
   repair.exact_conditions tests this; it agrees with brute force for q <= 5.
4. q odd: a local duality (M(Gamma_2(x)) = Gamma_2(M(x)) for x in R) on a non-friendly transition of Q(4,q) or W(q)
   exists only for |R| <= 2 (point triads of Q(4,q) have 0 or 2 centres, of W(q) 1 or q+1).
5. The smallest line cover of Q(4,3) (= smallest blocking set of W(3)) has 11 lines < q^2+q = 12. A SAT search finds
   non-friendly freed sets of size 2 in Q(4,3); larger sizes are being tested by the director.
6. Best 7-level typing over all regular tournaments: K_A + K_B = a + b + 4c, where a = cap of H->D transitions (ovoid of
   Q(4,q): q^2+1), b = cap of D->H (partial spread of Q(4,q) = partial ovoid of W(q); <= q^2-q+1 for q odd, Tallini),
   c = cap of non-friendly transitions.
7. Lab records at D = 5: (5,5) 354, (6,5) 684 (table), (7,5) 1,152, (8,5) 2,048, (9,5) 2,662, (10,5) 4,800,
   (11,5) 7,020, (12,5) 9,840, (13,5) 11,486, (14,5) 17,568, (15,5) 20,736, (16,5) 33,792.
   Level graph + hubs gives 11,480 + K_A + K_B at (13,5) (q = 9, r = 3) and 20,496 + K_A + K_B at (15,5) (q = 11, r = 3).
8. Doubled-matching lifts (research/d10D7/DM_D5.md) give 12(q+1)(q^2+1) at degree q+3; three copies over Z9 are ruled
   out by counting there.

Scoreboard: append exactly ONE line of JSON to research/squads/gqd5-r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command>", "score": <number>,
 "valid": true|false, "next": "<one line>"}
Reply to the director in at most 5 lines (what you found, the score, where the files are).
