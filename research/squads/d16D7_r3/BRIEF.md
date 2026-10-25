# Squad d16D7 r3: push the orbit-graph independent sets further (evolved from r2)

Same problem, files, scorer and rules as round 2: read /home/user/degree-diameter/research/squads/d16D7_r2/BRIEF.md
first (graphs og_pts.txt / og_lines.txt and ogscore.py are in research/squads/d16D7_r2/). Work in
`research/squads/d16D7_r3/<card>/`, heavy runs through `/home/user/degree-diameter/research/squads/d16D7_r3/run_slot.sh`
(same rules: nice, timeout, single thread, CPU budget 420 s per graph), append ONE JSON line to
`research/squads/d16D7_r3/scoreboard.jsonl`, reply in at most 5 lines.

What round 2 found: a k-fixed penalty tabu search (card c2, code research/squads/d16D7_r2/c2/ktabu.c, usage
`ktabu GRAPH SEED OUT CPU_SECONDS RNG_SEED [STALL_ITERS]`) is the best method: 235 (points) and 237 (lines) orbits in
420 s from the 224/227 seeds; ARW iterated local search reached 229-234, annealing 232, LNS 229, a memetic search 231,
min-degree greedy multistart 221. But the symmetric quotient search below beat them all (240/240).
Score = min(K_pts, K_lines); every orbit gained in the smaller one is +122 vertices of the (16,7) graph.

You may copy ktabu.c into your folder and modify it (keep the bucket structure; it is fast). Do not edit the r2 folders.

## Round 3 update: symmetric seeds win

The best round-2 result came from card c8 (geometric wildcard): **240 points and 240 lines**, from sets invariant
under two more collineations that normalise G (h of order 183 and a Frobenius map F of order 3; together a group of
order 9 acting on the orbit-graph vertices), annealed in the small quotient (8 s) and expanded. So symmetric
quotients are the lead. They are ready in `research/squads/d16D7_r3/quot/`:

| file | symmetry | quotient vertices (pts / lines) | weights |
|---|---|---|---|
| q9_*.txt | <h, F>, order 9 | 573 / 588 | mostly 9, some 3 and 1 |
| qF_*.txt | <F> | 2090 / 2041 | mostly 3, some 1 |
| qh_*.txt | <h> | 1944 / 2136 | mostly 3, some 1 |
| qhF_*.txt | <hF> | 2087 / 2032 | mostly 3, some 1 |
| qhF2_*.txt | <hF^2> | 2087 / 2032 | mostly 3, some 1 |

Quotient format: first line `n`, then per vertex `w deg nbr1 ... nbr_deg` (w = number of orbit-graph vertices it
stands for). An independent set of the quotient expands to an independent set of the orbit graph of total weight:
`python3 /home/user/degree-diameter/research/squads/cells/d16D7/ogquot_expand.py quot/qX_pts.map QSOL OUT` (MAP lines =
orbit-graph vertex indices), then score OUT with ogscore.py as before. Seeds `seed_pts.txt`, `seed_lines.txt` here are
c8's 240 sets. Card c8's weighted annealer is research/squads/d16D7_r2/c8/wsa.c (`wsa GRAPH OUT CPU_SECONDS SEED`,
same quotient format). k-fixed tabu: research/squads/d16D7_r2/c2/ktabu.c (orbit-graph format; adapt it to the quotient
format, e.g. by ignoring weights and filling the light vertices afterwards, or by a weighted penalty).

Typical pipeline for a card: (1) search the quotient (fast: small graph); (2) expand; (3) polish the expansion with
ktabu on the full orbit graph (`/home/user/degree-diameter/research/squads/d16D7_r2/c2/ktabu og_pts.txt START OUT 420 SEED`
through run_slot.sh), which breaks the symmetry where it helps. Report the quotient-level and the polished scores.
