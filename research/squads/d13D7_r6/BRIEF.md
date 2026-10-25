# Squad round 6 (job cell-13-7): beat 756 pairwise-opposite points of H(11)

Read research/squads/d13D7_r4/BRIEF.md (problem, scorer, rules) and the orbit-union code of rounds 3-4
(research/squads/d13D7_r3/c3/: orbl.py, wclq2.c, replay2.py; research/squads/d13D7_r4/c1/: sweep.py, runlog.jsonl).
Current best: 756 = research/squads/d13D7_r4/c1/best_idx.txt, the union of orbits of the cyclic group <h> of order 15,
h = a b^2, where a (order 15 on a 5-dim U) and b (order 5 on U^perp) commute (generators research/squads/d13D7_r4/c1/
best_gen.txt and research/squads/d13D7_r3/c3/best_gen.txt). The bigger group <a> x <b> gave 720 (exact optimum of its
orbit graph); LNS around 720 found nothing (locally rigid). Every extra point = +2 vertices at (13,7), +4 at (14,7),
+6 at (15,7). Rules as in round 4 (one heavy process at a time, `timeout 900 nice -n 10`, <= 600 s CPU per run,
<= 1.5 GB, no git, write only in research/squads/d13D7_r6/<card>/, best as <card>/best_idx.txt + generators, one JSON
line in research/squads/d13D7_r6/scoreboard.jsonl, reply in <= 5 lines). Time box about 30 minutes. The machine is
also running Opus's 4-thread graph checks.

c1: NON-ABELIAN groups: generate two non-commuting isometries of small order (2, 3, 4, 5, 6) and take the group they
    generate when it is small (closure <= 2000 elements; enumerate by BFS on matrices), e.g. dihedral, A4, S3 x Z5,
    Frobenius groups; orbits, exact/tabu max-weight clique.
c2: WARM-STARTED SUBGROUPS of the 756 group: the 756 set is a union of orbits of <h> (order 15); its subgroups <h^5>
    (order 3) and <h^3> (order 5) have bigger orbit graphs that still contain the 756 solution as a clique. Start the
    weighted tabu / exact search from that clique and look for heavier ones; also try overgroups <h, g> with g
    normalising <h>.
c3: NEW BLOCK SHAPES: commuting elements on orthogonal decompositions not tried in round 4 (see its runlog:
    research/squads/d13D7_r4/c1/runlog.jsonl), e.g. U of dim 4 + dim 3 with both factors of order 3, 5, 6, 10, 12,
    15, and three blocks 3 + 2 + 2; exact clique where the orbit graph is small.
