# Squad header for job raise-small-d (read this first, then your card)

Job: raise the lab's values of the bipartite degree-diameter cells (Δ, D) with Δ = 3, 4 and D = 9..14. A value is the
number of vertices of a bipartite graph with maximum degree Δ and diameter at most D. Repo: /home/user/degree-diameter.
Job folder (tools, binaries): research/frontier/raise_small/ (call it $RS). Your folder: research/squads/raise-small/<round>/<card>/.

## Values to beat (lab values; "census" = published Foster census, not ours)

| D | Δ = 3 | Δ = 4 |
|---|---|---|
| 9 | 506 (2013 table) | 4,970 (2013 table) |
| 10 | 810 | 12,416 |
| 11 | 1,474 | 30,334 |
| 12 | 2,368 | 74,066 |
| 13 | 3,648 (this job, round 0) | 192,382 |
| 14 | 5,706 (census CSS(6272,7) has 6,272: beat 6,272) | 497,042 |

## Tools (compiled in $RS/bin; sources in $RS/tools; do not edit them, copy into your folder if you change one)

- `gtab.py OUT m k r [c]`: multiplication table of G = (Z_m x|_r Z_k) x Z_c in the format below (identity = index 0).
  Format: header line "G N id name", then N*N integers (row g, column h = index of g*h). Several groups per file allowed
  (`--list FILE`). You may write your own generator for other groups in the same format (identity must be index 0).
- `glist.py Nlo Nhi [kmin] [dmin] [--odd] [--fpf]`: lists metacyclic groups "N m k r d fpf" (d = order of r mod m).
- `bin/salift_s p TAB id seed SECS [T0 T1] OUT.sol` (env D, START=file.best): joint simulated annealing of a p+p cubic
  bipartite base multigraph AND its voltages in the group (own-small job). Lift n = 2 p N. Cost = number of
  (base root, vertex) pairs at distance > D; 0 means diameter <= D. Writes OUT.sol.best on every improvement
  (header "N id p cost") and OUT.sol at cost 0. ~5-20k evaluations/s at n ~ 4,000.
- `bin/polish p TAB id START.best OUT.sol` (env D): exact 1- and 2-move steepest descent from a .best state (every single
  voltage change, every endpoint swap, every pair of voltage changes, swap + new voltage). Slow for N > 500 (minutes).
- `bin/salift4 ...`: the degree-4 version of salift (read its header in $RS/tools/os_salift4.c).
- `bin/hmeta d D secs seed K OUT m k r` (env THREADS=1, T0, T1, REHEAT, START, EVAL): Haar graphs H(G,S) of metacyclic
  groups, random S annealing, bit-parallel (beyond-d13). Header: $RS/tools/hmeta.c.
- `bin/lift`, `bin/liftd`, `bin/scan_h02`: cyclic (Z_n) voltage lifts of a fixed base ($RS/bases/*.txt), beyond-d13.
- `tools/sol2edges.py SOL m k r [c] OUT.edges`: edge list of a salift_s/polish solution (recomputes the group product).
- `tools/scanlift.sh D p LIST SECS OUTDIR [SEEDS]`: salift_s over each group line "N m k r ..." of LIST; checks finds.
- **Scorer / checker:** `bin/apsp EDGES d D` (all pairs, no symmetry assumed; prints RESULT VALID/INVALID). Every
  claimed graph must pass it at D and FAIL at D - 1 is a bonus. Edge list format: first line n, then "u v" per edge.

## Machine rules (4 cores and 15 GB shared by ~16 cards and the director)

- One process at a time, single-threaded (THREADS=1), always `timeout 110 nice -n 10 <cmd>`.
- **Every Bash command must finish in under 110 seconds.** Chain several short runs (use START=... .best files to continue
  an anneal). A longer command is moved to the background and you will sit idle; never use `&`, `nohup`, `sleep`.
- At most 1 GB of memory. No git commands. Write only inside your card folder. Do not kill processes you did not start
  (no pkill/killall). Do not use any remote-session or GitHub tools.
- Total time box: about 40 minutes of work, then report.

## Report

1. Append ONE line of JSON to research/squads/raise-small/<round>/scoreboard.jsonl:
   {"card": "<id>", "cell": "(3,13)", "idea": "<one line>", "code": "<path>", "command": "<exact command>",
    "score": <vertices of your best VALID graph, or 0>, "best_cost": <lowest cost reached above the target, with its n>,
    "valid": true|false, "next": "<one line>"}
2. If you have a VALID graph above the value to beat: keep its .sol (or voltage file) and its apsp output in your folder.
3. Reply in at most 5 lines.
