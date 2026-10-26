# Big squad, round 3: (4,9) mainly, plus a few (4,8) cards

## Goal
Most cards (d..): find a **bipartite graph with maximum degree 4 and diameter at most 9 on more than 4,970 vertices**
(the (4,9) table value; bipartite Moore bound 19,682). Any record has n >= 4,972. Cards e..: the (4,8) goal as before
(diameter <= 8, more than 2,184 vertices). Your card says which. Every tool takes D as an argument: use 9 for (4,9).

What is known for (4,9) (director, 05:10-05:20 UTC):
- 4,970 = 2 * 2,485 = 2 * (71 * 35): exactly a Haar graph of the Frobenius group Z_71 x| Z_35 (order 2,485). So the table
  is probably a metacyclic Haar graph, and the next Frobenius-type groups above 2,485 are the natural targets.
- For a Haar graph H(G, S) at D = 9 the binding side is the same side: words of even length <= 8 from (e, A), at most
  1 + 12 + 108 + 972 + 8,748 = 9,841 of them, must cover all N >= 2,486 elements (lambda ~ 4; easier than (4,8)'s ~3).
  These words are inverse-closed, so involutions get half the chances: avoid groups with many involutions
  (research/structured/STRUCTURE.md section 2, point 6).
- No good metacyclic group (k >= 6, faithful) exists at orders 2,486..2,495; the first useful order is 2,496 (n = 4,992).
- haar_fast 10 s screens (single run each): meta 101 25 5 (order 2,525, n = 5,050) cost 2; meta 104 24 7 and meta
  208 12 3 (2,496, n = 4,992) cost 4 (and 4 again after 240 s); meta 105 24 17 (2,520) cost 6.
- The director is running an exhaustive search on meta 101 25 5 (do not repeat it).

What is known for (4,8) after rounds 1-2 (74 cards, research/squads/LOG.md): no valid graph above 2,184. Haar graphs of
metacyclic and abelian-by-cyclic groups of order 1,093..1,450 have floors 1..30; an exhaustive search up to automorphism
proved Z_55 x|_2 Z_20 (order 1,100) cannot reach diameter 8 (its minimum is the cost-1 trap), so annealing floors are true
minima. Surgery on the valid 2,184 seed floors at 217 far pairs (n = 2,186).

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

- **exh_meta.py** (exhaustive Haar search over a metacyclic group, up to automorphism; needs gcd(r-1, m) = 1):
  `python3 $T/exh_meta.py m k r [--slice i/n] | LIMIT=2 ONLYLOW=1 $T/flift $T/bases/dipole4.txt meta:m:k:r 4 D eval`
  prints every S = {e, x, y, z} with cost <= LIMIT (flift convention, lift-style cost = 2 x haar_fast's on these traps)
  and the minimum on stderr. About 540k sets/s at (4,8), 150k/s at (4,9); a group of order ~2,500 takes ~9 CPU-min.
- haar_fast / haar_tab / lift / flift all take D: e.g. `THREADS=1 $B/haar_fast 4 9 10 1 8 out.txt meta 101 25 5 1`.
  build_haar2.py checks haar_fast solution files at any D (it reads D from the file).

## Score you report
- `n`: vertices of your best graph (even). `cost`: its cost from the tool you used (0 = valid). `miss` = cost per
  vertex: lift cost / b, haar_fast cost / 2, or 2*far_pairs/n from score48. Lower miss is better at equal n; any
  cost-0 graph with n >= 2,186 beats everything.
- A claimed valid graph MUST have an edge-list file that `$T/score48` reports as `RESULT VALID` (run it yourself and
  paste the RESULT line into "check"). For (4,9) run `$T/score48 FILE.edges 4 9`.

## Scoreboard: append exactly ONE line (JSON) at the end
File: /home/user/degree-diameter/research/squads/b48/r3/scoreboard.jsonl (append with `>>`, one line, valid JSON):
`{"card": "d07", "cell": "4,9", "idea": "<one line>", "code": "<path to your script>", "command": "<exact command for your best result>",
"n": 2200, "cost": 3, "miss": 1.5, "valid": false, "check": "<score48 RESULT line or tool RESULT line>",
"files": "<path to best edges/solution file, or empty>", "next": "<one line: what you would try next>"}`

## Machine rules (about 4 cores and 15 GB shared with up to 19 other cards and the director)
- Work ONLY in your folder /home/user/degree-diameter/research/squads/b48/r3/<card>/ (create it). No edits anywhere
  else, no git commands, never touch other cards' folders or the tools.
- Every heavy command: `THREADS=1 timeout 120 nice -n 10 <cmd>`. One heavy process at a time. Each search run at most
  60 s. Total CPU for your card at most about 5 minutes. Memory under 500 MB.
- Time box: about 25 minutes of wall time, then write the scoreboard line and stop.
- Write your own code in Python or C (gcc -O2 is available; numpy is available; networkx/scipy are NOT).
- Do not stop at analysis: run your strategy and report a real score, even if it is bad. An honest bad score is useful.
- Leave no process running when you finish (no background jobs).

## Reply to the director
At most 5 lines: best n and cost, whether score48 says VALID, the one idea, the file path.
