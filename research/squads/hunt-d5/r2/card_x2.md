# Card x2 (round 2)

Read ../r1/PREAMBLE.md and ../r2/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r2/x2/ (create it).

(6,5) NEW CELL (published value 684): route-chart lifts over F₂⁴ (degree 3·2 = 6, 32m vertices; m ≥ 22 beats
684). The q = 2 charts found so far (`../charts/chart_q2_dA1.txt`, `chart_q2_dB1.txt`) have 4+4 singular patterns and
fail the diagonal on one side, so that side needs nonsingular 4-cycles: `DIAG4A=1 ctrlpat m CHART …` reaches cost 26
at m = 20, 50 at m = 22. Improve: search charts with fewer singular patterns or with both diagonals (chartq 2 with
DIAG=1, WP/WD weights, many seeds), or anneal chart and controller jointly (write your own driver). Check any cost-0
controller with `python3 rcq.py 2 CTRL CHART X.edges` and `apsp X.edges 6 5`.
