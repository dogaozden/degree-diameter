# Squad gqd5-r2: additions to research/squads/gqd5-r1/PREAMBLE.md (read that first; same rules, tools, scoreboard format,
# but your folder is research/squads/gqd5-r2/<card>/ and the scoreboard is research/squads/gqd5-r2/scoreboard.jsonl)

STRICT CPU RULE for this round: at most ONE heavy process at a time, always `timeout 900 nice -n 10`, and NO process may be
left running when you reply (kill your background jobs first). The machine has 4 cores for 14 agents.

New facts from round 1 (do not redo):
9.  Records built by the director: (13,5) 11,621 = 11,480 + K_B 86 + K_A 55 (q = 9, 7 levels, rotational tournament
    j -> j+1, j+2, j+3, types HHHDHHD over G = Q4(9); H->D arcs free the ovoid of Q(4,9) (82); D->H arcs free a partial
    ovoid of W(9) of 51 points (= partial spread of Q(4,9)); every non-friendly arc frees a 2-point local duality;
    hub graph found by annealing).  Builder: research/theorems/d5gq/build_typed.py (env LD=1 for local dualities).
    q = 11 gives 20,696 (needs >= 20,737 to beat the lab's (15,5)).  In this layout K_B = a + 2c, K_A = b + 2c where
    a = 122 (q=11) / 82 (q=9), b = D->H freed set size, c = freed set size on each non-friendly arc (if a + c <= 2b).
10. Best partial ovoids found: W(9) 51, W(11) 70 (Tallini bound 73 / 111; files research/squads/gqd5-r1/c1/best_W9.json,
    c3/best_W11.json).  Uniform explicit family: only q+1 points.
11. Non-friendly arcs: the exact two-level criterion allows 3 freed points in Q(4,5) (c4, research/squads/gqd5-r1/c4/);
    with 7 levels, annealing the OTHER matchings repairs a random 16-point freed set on one non-friendly arc at q = 5
    (c19, research/squads/gqd5-r1/c19/).
12. Relaxed line sets on D->H arcs (director's analysis, Theorem E): if a freed line l meets exactly one other freed line m
    (at a point z), the only bad pairs are (l in the D-level, p in the H-level) and (p in the D-level, l in the H-level) for
    the q points p of m other than z.  They are repaired if the B-hub of the slot of l sits, in the H-level, at a freed
    point of m (e.g. the ovoid point of m), and the A-hub of the slot of l sits, in the D-level, at a freed B-slot point
    of m.  Needs z not on the ovoid.  In W(q) language: a set T of points of W(q) where every point is collinear with at
    most one other point of T and the joining line is not in the regular spread S.  Simple SA (research/theorems/d5gq/
    relaxed.c) finds |T| = 60 at q = 9 and 79 at q = 11.
