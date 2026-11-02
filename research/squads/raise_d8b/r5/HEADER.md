# raise-d8b round 5: shared rules for every card (read all of this first)

Job raise-d8b (Opus director, branch claude/raise-d8-d7-beyond-table-8mozbm). Goal: larger bipartite graphs of maximum
degree d and diameter 8 for d = 17..20 (cells beyond the 2013 table). Current values (all Haar graphs H(G,S), checked):

| cell | vertices (2N) | group, orbit structure ("k m f") |
|---|---|---|
| (17,8) | 43,463,280 | PSL(2,41) x Z631, "7 2 3" (r3/e01: its RANDORB screen picked k = 7; mu 41.2, 1,860 evaluations) |
| (18,8) | 64,792,896 | PSL(2,97) x Z71, "7 2 4" (r2/d06, orbits of order 7, mu 46.3, 2,140 evaluations) |
| (19,8) | 92,166,360 | PSL(2,131) x Z41, "5 3 4" (r2/d07, mu 35.9) |
| (20,8) | 131,610,120 | PSL(2,59) x Z641, "5 4 0" with ORBW=5 (r4/f04, mu 39.0, 2,156 evaluations) |

**Round 1 finding: orbits of order 5 (ORBIT "5 m f") solve far higher mu than order 3** (k = 3 at mu 28 sat at cost 3
after 12,000 evaluations where k = 5 at mu 29.6 solved in 97). Keep f small: the f - 1 fixed generators all lie in the
abelian centralizer of alpha, and three or more commuting letters make 6-cycles (round 1: "5 3 4" on sl 41 671 stuck
at cost 100, but on psl 109 71 it solved mu 34.5). Orbit order 9 was much worse than 3 (RANDORB). Order 7 is untested beyond one RANDORB.

**Round 2 finding: orbits of order 7 can beat order 5.** (18,8) "7 2 4" on psl 97 71 solved mu 46.3 in 2,140
evaluations; k = 5 "5 3 3" needed 18,549 at mu 44.2. Difficulty roughly follows mu/k (expected number of uncovered
orbits) plus alpha-fixed misses (a fixed element is missed with probability ~ e^(-lambda/k), lambda ~ 13). But at (17,8)
RANDORB put k = 7 "7 2 3" behind k = 5 "5 3 2" (sl 29 911: median 394 vs 91), and one orbit of 11 was hopeless (median
2,508). Which k wins depends on the group, so this round SCREENS before it searches.

**Round 3 findings.** (1) The RANDORB screen works: e01 picked k = 7 over k = 5 at (17,8) and solved in 1,860
evaluations. (2) k = 7 with many fixed letters is hopeless ("7 2 6" at (20,8): median/k 97-261 against 11-15 for "5 4 0").
(3) Hole anatomy (r3/e13): with f = 0 ("5 4 0") the last holes are alpha-FIXED elements (z = 0, in the torus of the
alpha element), each missed with probability ~e^(-lambda/5); with f = 3-4 the last holes are whole free orbits.
(4) New tool for (3): `$BIN/haar_big0w` = haar_big0 plus `ORBW=w`: an uncovered alpha-fixed element weighs w in the
search energy (the lab's (15,8) record used ORBW=5 with f = 0 in haar_sym). Use `ORBW=5` with haar_big0w for every
"5 4 0" run. Its log "cost"/"best" are weighted; best=0 still means solved.

**Round 4 finding (r4/f15, a fit over 74 runs of this job):** evaluations to solve ~ exp(1.0 + 1.21 mu/k); within one
1400-s run at ~0.2 core a solve is likely below mu/k ~ 6, possible up to ~8, and nothing solved above ~9. So k = 7 is
the way up where it is usable ((17,8) "7 2 3", (18,8) "7 2 4"); (19,8) and (20,8) stay at k = 5. Near misses at cost 5
are one orbit of 5 ("5 3 4") or one alpha-fixed hole ("5 4 0": haar_big0w with ORBW=5 shows it as cost 5).

**This round: each card runs ONE 1400-second search** (haar_big0, or haar_big0w with ORBW=5 where the card says so),
either fresh or continuing a saved state: first `cp` the named state file into your folder, then pass
`START=<your copy>` and the SEED named on the card. Never write outside your folder. Check any a.sol with haarcheck_gen.

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
- Work only in your folder /home/user/degree-diameter/research/squads/raise_d8b/r5/<card>/ (create it). No git
  commands. Do not edit any other file except appending your one scoreboard line.

## Scoreboard (one JSON line, appended at the end)
`echo '<json>' >> /home/user/degree-diameter/research/squads/raise_d8b/r5/scoreboard.jsonl` with
{"card": "g07", "cell": "(19,8)", "idea": "<one line>", "group": "psl 103 79", "command": "<exact search command>",
 "sol": "<path of the best .sol or .sol.best>", "score": <vertices 2N of your best VALID graph, or 0 if none>,
 "best_cost": <lowest cost reached on the largest group tried>, "valid": true|false, "evals": <total>, "next": "<one line>"}
Then reply in at most 5 lines. A Haiku's VALID is a claim; the director re-checks every find.

## Already found / already ruled out (do not repeat)
- Values above. The director is running (20,8) PSL(2,41) x Z1931 "5 4 0" ORBW=5 (mu 45.8), (17,8) SL(2,71) x Z61 "5 3 2" ORBW=5 from a one-fixed-hole state, (19,8) PSL(2,59) x Z451 "5 3 4" from a cost-5 state.
- Round 2: an alpha acting on one factor of PSL(2,41) x SL(2,5) x Z11 (non-abelian centralizer) has 2,400 fixed elements and screened far worse (median 2,935 vs 47); PSL(2,509) x Z1 at (20,8) is slow (1.5 s/eval) and stalled at 21; "7 2 3" on sl 29 883 stalled at 77.
- Round 2: cyclic/coset Haar graphs are bounded far below (r2/d16: |4D| counting bound); 2+2 lifts no better than Haar (r1/c16).
- Round 1 near the wall (cost 2-6 after ~2,000-8,000 evaluations at ~0.2 core): k = 5 at mu 35-46. At D = 8 the last holes are ordinary elements (r1/c09), not fixed points.
- k = 5 with f = 4 worked on PSL(2,109) x Z71 but stalled at cost 90-100 on SL(2,41) x Z671; k = 9 is bad; haar_sym product groups screened badly (r1/c13).
- Orbits of order 2 (involutions), z-only automorphisms, Heisenberg groups, field-automorphism orbits, single orbits,
  big cyclic factors with n/p > ~40, self-dual (transpose-closed) S, -I as a generator, moving the fixed generators:
  all worse (STRUCTURE.md sections 2, 5; job beyond-d11). Random S without orbits walls at mu ~ 21-25.
- Doubling a general (Delta-1, 7) graph: 2 n(16,7) = 30.0M < 41.4M, and the general table stops at degree 16.
- At even D (D = 8 here) PSL with n = 1 is fine (the odd-D involution problem does not apply).
