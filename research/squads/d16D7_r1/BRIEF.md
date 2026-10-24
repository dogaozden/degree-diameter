# Squad d16D7 round 1: make the joint-cover annealing solve more freed pairs per family

Goal: the bipartite (16,7) record. We hold 4,022,380 = 5·|H(13)| + 40 (20 freed pairs). The construction (see
`research/squads/cells/d16D7/d16hex.c`, header comment) is the table graph X(M1, M2) on five copies of the generalized
hexagon H(13) plus 2 hub vertices per "freed pair". Each freed pair j = (point p_j, line l_j = M1(p_j)) loses its M1 edges;
the graph keeps diameter 7 iff, for every pair, every point opposite p_j and every line opposite l_j is covered by a
short route. `fast_search` anneals over the bijection M1 (swaps of the lines of two points) with exact incremental route
counts; `zeros` = number of uncovered targets (the "proxy"; 0 means solved). `sig_init` builds the starting M1 by
matching points to lines with the same "signature" (set of pairs whose cover set S'(p_j) / S(l_j) contains them).

Today: 13 pairs solve in 9 s, 16 in 27 s, 20 in ~100 s, 24 in ~700 s (proxy 3452 at 600 s), 31 stalls at ~130K.
More pairs per family = more vertices (+2 each), so a faster or stronger search is worth real records.

## The benchmark (same for every card)

    HEX=/home/user/degree-diameter/research/squads/cells/d16D7/hex/hex_q13.bin
    BESTK=4 T0=0.3 /home/user/degree-diameter/research/squads/d16D7_r1/run_slot.sh ./d16hex search $HEX 28 7 450 out.sol 2 6 5 6

(28 pairs, seed 7, 450 s budget, mode 2 = PG(2,5) hub graph, alg 6 = signature init + annealing, freed points pairwise
opposite.) It prints `fast search (family 0) done: it .. acc .. proxy X (..s)` and finally `RESULT ...`. Your score is
X, the proxy when the annealing stops (lower is better; 0 = solved, then also report the time it took). The unmodified
code's run of this exact command is the baseline (Opus is running it now; just try to beat it. For scale: on 24 pairs
the unmodified code is at about 22K after 300 s and 3.5K after 600 s; on 28 pairs expect tens of thousands).

## Rules

- Work only in your folder `research/squads/d16D7_r1/<card>/`. Copy the base code there:
  `cp /home/user/degree-diameter/research/squads/d16D7_r1/base_d16hex.c d16hex.c`, edit, compile with
  `gcc -O2 -march=native -o d16hex d16hex.c -lm`.
- Every heavy run goes through `run_slot.sh` (it waits for one of 3 shared CPU slots, adds nice and a 1500 s wall-clock timeout; the 450 s budget is CPU time, so a shared box does not change scores).
  One benchmark run per card (a second only if the first finished and you have a clear fix). Never run anything heavy outside it. Memory per run is about 1 GB; fine.
- Keep the change focused: one idea, written as code. Don't touch other folders, no git commands.
- The proxy must stay exact: every counted route must be a real path in the graph (if you add route types or moves,
  keep the add/remove bookkeeping symmetric). If your run prints `RESULT ... VALID` the final BFS check passed.
- When done, append ONE line of JSON to `research/squads/d16D7_r1/scoreboard.jsonl`:
  `{"card": "c3", "idea": "<one line>", "code": "research/squads/d16D7_r1/c3/d16hex.c", "command": "<exact>",
  "score": <final proxy>, "solved": <true|false>, "secs_to_solve": <number or null>, "valid": <true|false>,
  "next": "<one line>"}` (use `echo '...' >> scoreboard.jsonl`), and reply in at most 5 lines.
