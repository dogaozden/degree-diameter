# raise-d8b round 2: shared rules for every card (read all of this first)

Job raise-d8b (Opus director, branch claude/raise-d8-d7-beyond-table-8mozbm). Goal: larger bipartite graphs of maximum
degree d and diameter 8 for d = 17..20 (cells beyond the 2013 table). Current values (all Haar graphs H(G,S), checked):

| cell | vertices (2N) | group, orbit structure ("k m f") |
|---|---|---|
| (17,8) | 41,723,520 | SL(2,31) x Z701, "5 3 2" (round 1, c03) |
| (18,8) | 62,842,200 | PSL(2,101) x Z61, "5 3 3" (director; mu 29.6 solved in 97 evaluations) |
| (19,8) | 88,597,200 | SL(2,101) x Z43, "3 6 1" (round 1, c08) |
| (20,8) | 126,119,280 | PSL(2,41) x Z1831, "5 4 0" (round 1, c11) |

**Round 1 finding: orbits of order 5 (ORBIT "5 m f") solve far higher mu than order 3** (k = 3 at mu 28 sat at cost 3
after 12,000 evaluations where k = 5 at mu 29.6 solved in 97). Keep f small: the f - 1 fixed generators all lie in the
abelian centralizer of alpha, and three or more commuting letters make 6-cycles (round 1: "5 3 4" on sl 41 671 stuck
at cost 100). Orbit order 9 was much worse than 3 (RANDORB). Order 7 is untested beyond one RANDORB.

**This round: every card runs ONE given rung (one group, one orbit type) for a full 1400-second haar_big0 run**, and
only if it solves early, checks it and moves to the next rung named on its card. No ladder from the bottom.

Any VALID graph with more vertices than the current value of its cell is a result. The size law (mu as above, W from
research/frontier/beyond/plan.py) says how hard a group order is: the orbit search solved mu ~ 23 in ~3,000 evaluations
and mu ~ 43 in ~3e5 at small sizes (research/structured/STRUCTURE.md section 3); the lab's best D = 8 records sit at mu ~ 50.
Vertices at mu = 30: (17,8) 42.5M, (18,8) 62.9M, (19,8) 91.1M, (20,8) 129.4M.

## Tools (already built; do not rebuild unless your card says so)
BIN=/home/user/degree-diameter/research/frontier/raise_d8/bin, GRP=/home/user/degree-diameter/research/frontier/raise_d8/grp.py
- `$GRP d D mu_lo mu_hi [k] [lines] [nmax] [pmin] [pmax]`: groups SL(2,p) x Z_n / PSL(2,p) x Z_n usable with an
  automorphism of order k (default 3), with their mu. Example: `$GRP 19 8 22 30 3 20`.
- `$BIN/haar_big0 d D SECONDS SEED K OUT sl|psl p n` (search; source research/frontier/beyond11/haar_big0.c, header
  comment = manual). Env: `ORBIT="k m f"`: S = e + (f-1) alpha-fixed generators (drawn at random from SEED once, never
  moved) + m alpha-orbits of size k, d = f + k m; f = 0 means m free orbits, no e (only for k | d). `THREADS=1` always.
  `START=file` continues from a saved S (`OUT.best` for f >= 1, `OUT.orb` for f = 0). `RANDORB=m`: costs of m random
  symmetric S (cheap screening, no search). `EVAL=file UNCPRINT=1`: list the holes of a saved S. K = 8 is normal.
  Speed: ~0.035 s per evaluation at N = 3e7 on a free core (much less on this shared box). Memory is tiny (N/2 bytes).
  Log lines `t=.. step=.. evals=.. cost=.. best=..`; on success a line starting `RESULT` and the file OUT is written.
- `$BIN/haar_sym` (research/structured/haar_sym.c, README in research/structured/README.md): slower (~0.15 s/eval at
  N = 3e7) but more group families (prod, sl over GF(2^k) with poly, meta, pgl) and ORBW. Use only if your card says so.
- Scorer (independent checker, BFS from both sides): `OMP_NUM_THREADS=1 nice -n 10 $BIN/haarcheck_gen OUT` must print a
  line starting `VALID`. ~30 s at N = 3e7, ~70 s at N = 6.5e7 on one core. Run it on every cost-0 find.

## Machine rules (4 cores and 15 GB shared by ~17 searches)
- At most ONE search process of yours at a time, `THREADS=1`, prefixed `nice -n 10`. Memory below 1.5 GB.
- Every Bash command must finish within 110 s. Start a search in the background and poll it:
  `cd DIR && nohup env ORBIT="3 6 1" THREADS=1 nice -n 10 $BIN/haar_big0 19 8 1500 1 8 a.sol psl 103 79 > a.log 2>&1 & echo $!`
  then repeat `sleep 100; tail -n 2 a.log` (each such command < 110 s). Do not end your work while your process
  runs: kill it by PID (`kill <pid>`) when you stop. Never use `pkill -f` or `killall`.
- Time box: 27 minutes of wall clock from your first command (one 1400-s run plus checks). Then stop, kill your process, write the scoreboard line.
- Work only in your folder /home/user/degree-diameter/research/squads/raise_d8b/r2/<card>/ (create it). No git
  commands. Do not edit any other file except appending your one scoreboard line.

## Scoreboard (one JSON line, appended at the end)
`echo '<json>' >> /home/user/degree-diameter/research/squads/raise_d8b/r2/scoreboard.jsonl` with
{"card": "d07", "cell": "(19,8)", "idea": "<one line>", "group": "psl 103 79", "command": "<exact search command>",
 "sol": "<path of the best .sol or .sol.best>", "score": <vertices 2N of your best VALID graph, or 0 if none>,
 "best_cost": <lowest cost reached on the largest group tried>, "valid": true|false, "evals": <total>, "next": "<one line>"}
Then reply in at most 5 lines. A Haiku's VALID is a claim; the director re-checks every find.

## Already found / already ruled out (do not repeat)
- Values above. The director is running (18,8) PSL(2,79) x Z131, "5 3 3" (mu 44).
- k = 5 with f = 4 (e + 3 commuting fixed letters) is bad; k = 9 is bad; haar_sym product groups screened badly (r1/c13).
- Orbits of order 2 (involutions), z-only automorphisms, Heisenberg groups, field-automorphism orbits, single orbits,
  big cyclic factors with n/p > ~40, self-dual (transpose-closed) S, -I as a generator, moving the fixed generators:
  all worse (STRUCTURE.md sections 2, 5; job beyond-d11). Random S without orbits walls at mu ~ 21-25.
- Doubling a general (Delta-1, 7) graph: 2 n(16,7) = 30.0M < 41.4M, and the general table stops at degree 16.
- At even D (D = 8 here) PSL with n = 1 is fine (the odd-D involution problem does not apply).
