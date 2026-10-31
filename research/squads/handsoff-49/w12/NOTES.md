# w12 NOTES (lifts of small 4-regular bipartite bases over simple / centreless groups, tabu)

Start: 2026-10-31 23:23 UTC. Stop (2 hours): about 01:25 UTC.

## Setup (done)
- groups/: PSL(2,8) 504 (psl2_8.bin, built from GF(8) on 9 points), PSL(2,9)=A6 360 (psl9.bin), PGL(2,9) 720 (pgl9.bin),
  S6 720 (s6.bin), M10 720 (m10.bin), PGL(2,7) 336 (pgl7.bin), PSL(2,11) 660 (psl11.bin), PGL(2,11) 1320 (pgl11.bin),
  PSL(2,13) 1092 (psl13.bin). Built by mkgroups.py (checked: involution counts match the known values).
- bases/: 4-regular connected bipartite multigraphs on h+h vertices: h=2 (2 classes), 3 (6), 4 (31; w5's exhaustive
  list), h=5 (30 sampled), h=7 (30 sampled), h=8 (30 sampled). Format: "2h" then edge lines (gen_bases12.py).
- wt12 = w8's wt.c (tabu over cotree voltages, cost = far (root, vertex) pairs; far unordered pairs = cost*K/2).
  Checked: the cost-0 lift of PSL(2,8) over the 2+2 base is VALID at D=9 under apsp, INVALID at D=8.
- Speed: about 1 ms per evaluation for b=10, K=504 (about 1,000 evals/s); NS=100 gives more iterations than NS=300.

## Plan
1. Screen 78 (group, base) pairs with 20 s tabu each (pairs_screen1.tsv, screen.sh -> screen1.tsv).
2. Deepen the best 6 with restarts (5 min, several seeds). 3. Record any cost-0 lift with n > 4970 to records/.

## Status 23:40 UTC
- Screen 1 running in the background (screen.sh, 20 s per pair, NS=100, TT=20): PGL(2,11) with 2+2 bases gives cost 88-91
  (n = 5,280); PSL(2,11) with 4+4 bases gives 136-163 (n = 5,280). Full table: w12/screen1.tsv.
- New tool wtt.c (wtt): tabu whose candidate moves come from far pairs. For a far (root x, lift vertex (y,g)) it samples
  base walks x -> y that use one cotree edge c once and solves the voltage of c that makes the walk end at (y,g).
  cmp_tools.sh compares wt12 and wtt for 60 s each on PGL(2,11) 2+2 (mh2_1), after the screen.
- Expectation from the walk count: same-side targets get about 3.7 walks each for any base (n about 5,000), so random
  lifts miss about 2.5 % of same-side pairs. Cost 0 needs structure; simple-group lifts are likely to stop at cost 10-50.
