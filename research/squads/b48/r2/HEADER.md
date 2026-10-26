# Big squad (4,8), round 2: rules every card follows

## Goal
Find a **bipartite graph with maximum degree 4 and diameter at most 8 on more than 2,184 vertices** (the record is
2,184; the bipartite Moore bound is 6,560). Bipartite, so any record has an even vertex count n >= 2,186.
Bigger is better, but n = 2,186 already is a world record. Near misses (a graph with a few far pairs) are useful too:
the director evolves the best ideas into the next round.

What is known after round 1 (48 cards; log in research/squads/LOG.md, board in r1/scoreboard.jsonl):
- Valid 2,184 seeds: research/squads/b48/seeds/haar_meta_91_12_25_*.edges (Haar graphs of Z_91 x|_25 Z_12; haar_fast
  solution files sol_91_12_25_*.txt next to them). It is the only group of order 1,092 found to reach cost 0.
- Metacyclic Haar graphs above 1,092 stall: order 1,100 (Z_55 x|_2 Z_20) at cost 1 (a local trap: one B-side element
  at distance 9, no cost-0 neighbour; 7 cards fell into it), other orders at cost 7..14.
- New family (director): split abelian-by-cyclic groups G = M x| Z_k, M a sum of finite fields F_{p^f}, the generator
  of Z_k multiplying component i by a primitive d_i-th root of unity (metacyclic = all f = 1). Screens with haar_tab:
  (Z_5 + F_8) x| Z_28 (order 1,120, n = 2,240) cost 3; Z_7^2 x| Z_24 (F_49, d = 24; 1,176, n = 2,352) cost 4;
  Z_13^2 x| Z_7 (1,183, n = 2,366) cost 6 (hard floor on 3 seeds); scalar actions (e.g. Z_17^2 x| Z_4 with the same root
  on both coordinates) are terrible.
- Surgery (card c31): delete 3 edges a_i b_i of a valid 2,184 seed, add a new vertex x (side A) adjacent to b_1, b_2, b_3
  and y, and y (side B) adjacent to a_1, a_2, a_3 and x: n = 2,186 with only 247 far pairs, all at distance 9, local
  (x: 23, y: 19, the rest around the deleted edges). Deleting one seed edge alone makes 165..180 pairs far.
- Weak in round 1: abelian lifts, lifts of Moore/girth-6/8 bases (PG(2,3), GQ(3,3)), Cayley graphs, coset graphs, plain
  graph annealing, orbit-symmetric S, wreath/direct products of non-abelian groups, Heisenberg groups.
Counting fact: from any vertex at most 3,280 vertices of the other side lie within distance 7; each side has >= 1,093.

## Tools (absolute paths; already built; do not rebuild them in place)
T=/home/user/degree-diameter/research/squads/b48/tools, B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin

- **score48** (the scorer for ANY graph): `$T/score48 FILE.edges` where FILE.edges is "n" on the first line, then
  one edge "u v" per line (0-based). Prints degrees, bipartite yes/no, diameter, far_pairs (unordered pairs at
  distance > 8), and `RESULT VALID ...` or `RESULT INVALID ...`. Takes well under a second at n ~ 2,200.
- **lift** (voltage-lift annealer over any finite group): `$T/lift BASE GROUP 4 8 SECONDS SEED [K] [OUT]`
  - BASE: text file "b m" then m lines "u v" (base multigraph, b vertices; u == v is a loop, degree 2; a third token
    "s" on a loop = semi-edge, degree 1, voltage an involution; a third integer token = fixed voltage).
    Ready-made bases in $T/bases/: dipole4.txt (Haar graphs), b22_t1.txt, b22_t2.txt (2+2 vertices), k33_matching.txt
    (3+3), k44.txt (4+4), bouquet_2loops.txt, bouquet_4semi.txt, bouquet_1loop_2semi.txt (Cayley graphs; the lift
    must come out bipartite, which lift checks for non-bipartite bases).
  - GROUP: `cyc:n`, `meta:m:k:r` (Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l), index a + m*j), or a table file
    made by groups.py (`.bin`).
  - The lift has n = b*N vertices; vertex (v, x) is v*N + x; edge (u,v,g) gives (u,x) ~ (v, x*g).
  - Cost = sum over the b base vertices u of the number of lift vertices farther than 8 from (u, e). Cost 0 = valid
    (diameter <= 8). It stops at cost 0. With OUT it writes the best state to OUT and the lift edge list to OUT.edges.
  - Batch scorer: `$T/lift BASE GROUP 4 8 eval < VOLT` scores many voltage assignments (one line per assignment,
    m group indices in the edge order of BASE, tree edges included), printing one cost per line. About 20,000/s at
    n ~ 2,200. Use it to score any family you enumerate yourself.
  - Env knobs: T0, T1 (temperatures, default 3 and 0.05), EPOCH (steps per cooling cycle, 20000), NOTREE=1, QUIET=1.
- **groups.py** (group tables): `python3 $T/groups.py "SPEC" OUT.bin` writes the multiplication table; without OUT it
  prints N, involutions, centre size. SPEC: `cyc n`, `meta m k r`, `dih n`, `semi p k a b c d` (Z_p^2 x| Z_k by the
  matrix [[a,b],[c,d]] mod p, its order must divide k), `sl2 p`, `psl2 p`, `pgl2 p` (p prime), `agl1 p`, `heis p`,
  `perm n g1 ; g2 ; ...` (permutation group, images comma-separated), and direct products `A x B x ...`.
  Python API: `sys.path.insert(0, T); import groups; groups.table(spec)` gives the numpy table.
- **haar_fast** (fastest Haar-graph annealer, about 10^6 evaluations/s, only for its built-in group families):
  `THREADS=1 $B/haar_fast 4 8 SECONDS SEED 8 OUT.txt GROUP... n` with GROUP one of `meta m k r`, `sl q`, `psl q`,
  `pgl q`, `agl1 q`, `prod G1 G2`, `cyc`, followed by n (a direct factor Z_n; use 1 for none). Example:
  `THREADS=1 $B/haar_fast 4 8 30 1 8 out.txt meta 55 20 2 1`. Prints `RESULT ... best=<cost>`; cost = uncovered
  elements on side A + side B (same as lift's cost for the dipole). On cost 0 it writes OUT.txt; turn it into an edge
  list with `python3 /home/user/degree-diameter/research/frontier/build_haar2.py OUT.txt OUT.edges`, then run score48.
  `$B/haar_sym` is the orbit-symmetric variant (see /home/user/degree-diameter/research/structured/README.md).

- **haar_tab** (haar_fast plus group family `tab FILE.bin`, any group table): `THREADS=1 $B/haar_tab 4 8 SECONDS SEED 8
  OUT.txt tab G.bin 1`. On cost 0 it writes OUT.txt; edges: `python3 $T/haar_tab_edges.py OUT.txt OUT.edges`. Prints
  `RESULT ... best=<cost>` (cost as haar_fast). It does not save near misses; use lift with the same table for that.
- **abc.py** (split abelian-by-cyclic groups): `python3 $T/abc.py build "k p:d,p:d,..." G.bin`, e.g. "28 5:4,2:7"
  = (F_5 with a 4th root, F_8 with a 7th root) x| Z_28; a component "p:d@e" uses w^e instead of w (so "17:4,17:4@3"
  is Z_17^2 x| Z_4 acting by diag(u, u^3)); d must divide k and not be divisible by p; f = ord_d(p) is automatic.
  `python3 $T/abc.py list LO HI --nonmeta` lists groups with <= 3 components, all d >= 3, order in [LO, HI].
- **farlist** `$T/farlist FILE.edges [8]`: prints every far pair "u v dist" and, on stderr, a summary.
- **edgecrit** `$T/edgecrit FILE.edges [8] [FIRST] [COUNT]`: for each edge, how many pairs become far if that one
  edge is deleted (a few ms per edge at n ~ 2,200).

## Score you report
- `n`: vertices of your best graph (even). `cost`: its cost from the tool you used (0 = valid). `miss` = cost per
  vertex: lift cost / b, haar_fast cost / 2, or 2*far_pairs/n from score48. Lower miss is better at equal n; any
  cost-0 graph with n >= 2,186 beats everything.
- A claimed valid graph MUST have an edge-list file that `$T/score48` reports as `RESULT VALID` (run it yourself and
  paste the RESULT line into "check").

## Scoreboard: append exactly ONE line (JSON) at the end
File: /home/user/degree-diameter/research/squads/b48/r2/scoreboard.jsonl (append with `>>`, one line, valid JSON):
`{"card": "c07", "idea": "<one line>", "code": "<path to your script>", "command": "<exact command for your best result>",
"n": 2200, "cost": 3, "miss": 1.5, "valid": false, "check": "<score48 RESULT line or tool RESULT line>",
"files": "<path to best edges/solution file, or empty>", "next": "<one line: what you would try next>"}`

## Machine rules (about 4 cores and 15 GB shared with up to 19 other cards and the director)
- Work ONLY in your folder /home/user/degree-diameter/research/squads/b48/r2/<card>/ (create it). No edits anywhere
  else, no git commands, never touch other cards' folders or the tools.
- Every heavy command: `THREADS=1 timeout 120 nice -n 10 <cmd>`. One heavy process at a time. Each search run at most
  60 s. Total CPU for your card at most about 5 minutes. Memory under 500 MB.
- Time box: about 25 minutes of wall time, then write the scoreboard line and stop.
- Write your own code in Python or C (gcc -O2 is available; numpy is available; networkx/scipy are NOT).
- Do not stop at analysis: run your strategy and report a real score, even if it is bad. An honest bad score is useful.
- Leave no process running when you finish (no background jobs).

## Reply to the director
At most 5 lines: best n and cost, whether score48 says VALID, the one idea, the file path.
