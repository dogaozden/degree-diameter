# Squad round sd5c-r1: (13,5) above 11,700 with self-dual Haar graphs

Goal: a 13-regular bipartite graph of diameter 5 on MORE than 11,700 vertices (ours now: 11,700). Here: a self-dual
Haar graph H(G, S), |S| = 13, of a group G of order N >= 5851.

## What is known (Opus, this session)
- Tool: `/home/user/degree-diameter/research/selfdual-d5c/src/fsd` (source `fsd.c` next to it; read its header comment).
  `K=13 ./fsd meta m k r n3` | `aff p f k n3` | `psl p n3` | `sl p n3` builds G = H x C_n3 from a formula, makes the
  self-dual "records" (involutory automorphisms beta, psi(x) = beta(x)^-1, S = e + psi-fixed elements + psi-pairs) and
  runs a tabu search with energy |G \ X X| (X = S^-1 S; energy 0 means diameter <= 5, then a full check prints "SOL").
  Useful env: K=13 TYPES=1,3 (f = number of psi-fixed elements in S; f = 1 and 3 work best) SECS=<s per record and
  type> STOPFIRST=1 MAXSOL=1 SEED=<n> TBUDGET=<total s> EDGES=<file for the first solution's edge list> RECS=1 (list
  records only) REC=<only this record>.  Output: one "TABU rec .. f .. best B ..." line per (record, type); B = lowest
  energy reached.
- Calibration at K = 13: C41 : C110 (meta 41 110 4 1, order 4,510) solved in 22 s; C251 : C20 (meta 251 20 32 1,
  order 5,020) solved in 83 s; C61 : C90 (5,490) best 12; C61 : C96 (meta 61 96 21 1, 5,856) best 20; C163 : C36
  (meta 163 36 23 1, 5,868) best 22 (60 s per type). So typical groups stop between 5,020 and 5,490; we need an
  exceptional group or a better method.
- Opus is screening every group of order 5851-5950 of the kinds meta / meta x C_n3 / aff / psl (list
  `/home/user/degree-diameter/research/selfdual-d5c/logs/wl13_all_5851_5950.txt`). Do not repeat that screen.
- sigma-invariant self-dual sets (S also invariant under an automorphism of order 2 or 3) are much worse. Don't redo.

## Scorer (the same for every card)
score = the lowest energy B over the TABU lines of an fsd run (or your variant) on a group of order N >= 5851 at K = 13
(lower is better, 0 = a candidate). "valid": true only if you got a SOL line AND
`/home/user/degree-diameter/research/selfdual-d5c/src/apsp_mt EDGEFILE 13 5 1` prints RESULT VALID. Algorithm cards
(new search method) report their best energy on the stated benchmark group instead.

## Machine rules (shared machine: 4 cores, 15 GB, Opus runs 2-4 jobs)
- ONE process at a time, single thread. Wrap every heavy command: `timeout 900 nice -n 10 <cmd>`.
- At most ~1.5 GB memory. Total time box: about 15 minutes of wall clock.
- Work only in your card folder `/home/user/degree-diameter/research/squads/sd5c-r1/<card>/` (copy fsd.c there if you
  change it; compile with `gcc -O3 -march=native -o fsd_x fsd.c`). No git commands. Do not edit files elsewhere.
- Never contact anyone or post anything outside the repo.

## Report
Append ONE line of JSON to `/home/user/degree-diameter/research/squads/sd5c-r1/scoreboard.jsonl`:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "group": "<fsd
group args>", "N": <order>, "score": <best energy>, "valid": true|false, "next": "<one line>"}
Then reply in at most 5 lines.
