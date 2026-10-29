# Squad round conics2-r1 (job conics-2, 2026-10-29)

Two questions about the diameter-7 level graphs (research/synthetic/CONICS.md 3.4; D7_HEXAGON.md on branch
claude/d7-hexagon-theorems-4w1prt, Definitions 1.3, 3.1, 3.2, Theorems B and C, Proposition 5.2).

A. Non-friendly transitions. Two copies of H(q) (level 0, level 1); matching edges (p,0) ~ (sigma(p),1) for every point
   p not in a freed set R, sigma a bijection points -> lines. The transition is *repaired* when every level-0 vertex is
   within 7 of every level-1 vertex. The records free R on such transitions with sigma a local duality at R (Theorem C):
   81 points at q = 5 (the (7,7) record 23,598 = 23,436 + 2*81), 295 at q = 7, 768 at q = 11, 792 at q = 13.
   GOAL A: a repaired transition at q = 5 with |R| > 81 (any sigma), or evidence that 81 is the limit.
   Scorer: python3 research/squads/conics2-r1/tools/transcheck.py data/hex_q5.bin SIGMA R  -> bad_pairs (0 = repaired)
   SIGMA = file of N = 3906 line indices (sigma[p], p = 0..3905), R = file of point indices. Start from the record:
   research/frontier/sols/d7D7_hex5_mirror81_n23598.sol ("multi" format: line 2 = "freed" + the 81 points, lines 4.. =
   sigma); `transcheck.py data/hex_q5.bin <that .sol> -` scores it (0 bad pairs). Freeing one more point gives ~600.
   One call takes ~0.3 s; you can import bad_pairs(q, N, LP, PL, sig, R) from tools/transcheck.py.

B. Dual segment sets: sets G of lines such that, for each line of G, the other lines of G meeting it all pass through
   one point of it. Upper bound (q+1)(q^3+1), reached only by the pencils of an ovoid (impossible for q even and for q
   prime >= 5). Our construction: the lines meeting a spread line v plus an exact whisker set, q(q^3+1) lines
   (q = 4: 260, q = 5: 630, q = 7: 2408; data/RL_whisk_q*.txt). GOAL B: a larger dual segment set at q = 2, 4, 5 or 7,
   or a proof by computer (exact ILP/SAT) that q(q^3+1) is the maximum at small q (q = 2: 18 vs bound 27; q = 4: 260
   vs 325).
   Scorer: python3 research/squads/conics2-r1/tools/dualseg_check.py data/hex_q{q}.bin FILE -> size, valid

Data (research/squads/conics2-r1/data/): hex_q{2,3,4,5,7}.bin (format: int32 q, N, L; L*(q+1) int32 point ids per line;
N*7 uint8 coordinates; load with tools/hexload.py -> q, N, LP (line -> its points), PL (point -> its lines), X);
RL_whisk_q{4,5,7}.txt, RH_spread_q{4,5,7}.txt (the spread's points), spread_lines_q{4,5,7}.txt (last line "# v = ...").
Python: numpy, python-sat (pysat, CaDiCaL), pulp + highspy (HiGHS MILP). C compiler available.

Rules: about 4 cores and 15 GB are shared with the main session and 7 other cards: one thread (THREADS=1), wrap
heavy commands as `timeout 900 nice -n 10 <cmd>`, at most 1 GB of memory, no git commands, write only inside your card
folder research/squads/conics2-r1/<card>/. Time box: about 20 minutes. Do not contact anyone or post anything.
When done, append ONE line of JSON to research/squads/conics2-r1/scoreboard.jsonl:
{"card": "cN", "goal": "A|B", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <|R| with 0 bad
pairs (A) or dual segment set size (B), or the proved maximum>, "valid": true|false, "next": "<one line>"}
and reply in at most 5 lines. Save any improving set (R and sigma, or G) as files in your folder.
