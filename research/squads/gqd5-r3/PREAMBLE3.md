# Squad gqd5-r3: read research/squads/gqd5-r1/PREAMBLE.md and research/squads/gqd5-r2/PREAMBLE2.md first (same rules,
# tools, scoreboard format), but your folder is research/squads/gqd5-r3/<card>/ and the scoreboard is
# research/squads/gqd5-r3/scoreboard.jsonl.  STRICT: one heavy process at a time, `timeout 1200 nice -n 10`, nothing left
# running when you reply.

New since round 2:
13. (13,5) record now 11,636 = 11,480 + K_B 86 + K_A 70: the D->H arcs free a RELAXED set of 66 lines of Q(4,9) (= 66
    points of W(9) found by card r2c1: every point collinear with at most one other, joining line not in the regular
    spread S; 30 pairs).  research/theorems/d5gq/graphs/d13D5_q9_relaxed66_n11636.json.
14. The hub rule only needs the A-hub condition (Proposition 7.2 of research/theorems/D5_QUADRANGLE.md), so there is NO
    limit on the number of partner pairs: K_A = |T| + 4 for any relaxed set T.  So every extra point of a relaxed set of
    W(9) adds one vertex to (13,5), and at q = 11 a relaxed set of 111 points of W(11) would beat the lab's (15,5)
    (20,736).  Counting bound: |T| <= 2(q+1)(q^2+1)/(2q+1) = 86 (q=9), 127 (q=11).  Best known: 66 (q=9), 87 (q=11).
    Tools: research/squads/gqd5-r2/c1/tabu.c (q=9, input in_W9.txt), research/squads/gqd5-r2/c2/ktabu.c (q=11, graph.txt,
    sline.txt; it also found that the spread stabiliser contains an elementary abelian group of order q^2 and diagonal
    symmetries, research/squads/gqd5-r2/c2/syms.json, struct.json), research/theorems/d5gq/relaxed.c, mk_relaxed.py.
    Verification of a relaxed set: research/squads/gqd5-r2/c2/verify.py (q=11), research/squads/gqd5-r2/c1/verify_T9.py.
