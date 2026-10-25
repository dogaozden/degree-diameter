# Squad round table-audit-r2 (2026-10-25)

Goal: a cubic bipartite graph of diameter 10 with at least 800 vertices, i.e. the table's (3,10) = 800 (credited to
Delorme–Gómez–Quisquater, never published, not beaten by the repo; Conder's C720.3 has 720). Round r1 got within 22
(symmetric SA, b = 16, c = 50) and 38 (Q3 lifts) unreached pairs. Scorer: `bin/apsp EDGES 3 10` must print
`RESULT VALID` with n >= 800. bin/ holds binaries compiled from repo sources (not committed).

## Result (07:28–07:54 UTC)
No card reached 800. Best per card (scoreboard.jsonl; costs are unreached ordered pairs unless noted):
c1 symmetric SA, (b, c) = (10, 80): 8 summed over orbit representatives (640 ordered pairs); c3 Haar over
SL(2,3) × Z17 (816 vertices): 22; c4 exhaustive Haar H(G, {e, a, b}) over 172 groups of order 400: none, best 10;
c2 Q3 over Z20 × Z5: 40; c6 joint base and voltage SA, b = 20 over Z40: 40; c5 Heawood over Z58 (812): 42;
c8 growing C720.3 by 40 gadgets: 961; c7 2-switch SA: VALID only at 500. The lead re-ran bin/apsp on c7/t500.txt
(VALID, 500), c8/g2_run.edges and c6/z40_b20_r1_best.edges (both diameter 11).
c4/tables/ (97 MB of group tables) is not committed; c4/run_c4.py writes it again. Compiled binaries are not committed either.
