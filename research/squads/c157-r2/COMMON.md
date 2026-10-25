# Squad c157-r2: common brief (cell (15,7), Opus job cell-15-7, 2026-10-24)

Repo root: `/home/user/degree-diameter`. Work ONLY in your card folder `research/squads/c157-r2/<card>/`
(copy any tool you want to change into your folder first). No git commands that change anything (no add/commit/push).

## The cell and what we already have
Goal: a bipartite graph of max degree 15 and diameter 7 with more than **2,480,184** vertices (the table value).
2,480,184 = 7·|H(11)|: seven copies (c ∈ Z_7) of the incidence graph of the generalized hexagon H(11)
(N = 177,156 points and 177,156 lines, degree 12, diameter 6), plus cross edges (p,c) ~ (M(p), c+j), j = 1,2,3,
for a bijection M: points → lines. Diameter ≤ 7 holds for EVERY bijection M.

We beat it with **hubs** (Opus, this session): pick K "freed flags" (p_a, l_a) with p_a on l_a and M(p_a) = l_a; delete
p_a's 21 cross edges and add 6 hub vertices per flag (3 adjacent to the 7 copies of p_a, 3 adjacent to the 7 copies of
l_a): **n = 2,480,184 + 6K**. Done so far: K = 8 → 2,480,232 (valid). The graph stays at diameter 7 iff
(1) every freed point/line still reaches everything within 7, and (2) hubs are pairwise close (a "hub graph").
(1) holds if M keeps an *exact cover* for every flag: with
S'(p_a) = {points u: d(u,p_a)=4, d(u,l_a)=5}, S(l_a) = {lines N: d(N,l_a)=4, d(N,p_a)=5},
every line of S(l_a) must have M⁻¹ at distance 4 from p_a, and every point of S'(p_a) must have M(·) at distance 4 from
l_a. One flag is trivial (map S' onto S). Many flags conflict: the conflicts are the bottleneck for large K.
(2) needs a bipartite "hub graph" between the K line-side hubs and the K point-side hubs (one of each per flag gets
the hub-graph edges), max degree 8, in which ANY two line-side hubs have a common neighbour and ANY two point-side hubs
have a common neighbour. K ≤ 8: complete bipartite (files `kkK.hg`); K = 57: PG(2,7) incidence (`pg27.hg`).

## Tools (all in research/d15D7/, already compiled; hexagon table hex/hex_q11.bin)
- `cover_match HEX K SEED ROUNDS OUT.sol HG PLACE`: places K flags (PLACE 0 random, 1 points pairwise opposite,
  2 read "p l" lines from the file named by env FLAGS), finds the bijection M by Hopcroft–Karp on compatible pairs,
  prints `RESULT K=.. unmatched-after-matching U, leftover cost C`. **C = 0 means all K flags keep exact covers.**
  HG = `noneK.hg` (file "K 0") is fine for experiments. Needs `ulimit -s unlimited`. K ≤ 64. ~10–25 s per run.
- `d7hexr search HEX K SEED SECS DONE.sol 3 2` with env `INIT=OUT.sol SKIPFULL=1`: local search that finishes a
  cover_match start (also uses other, "type-2", routes). Progress lines "proxy X" on stderr (0 = done); stdout
  `RESULT ... freed sources OK` when solved.
- `kcopy_hub check HEX DONE.sol 3`: exact BFS check of the (15,7) graph from all freed sources and hubs
  ("-> OK" = valid, given a valid hub graph in the file).
- `regions HEX K SEED MODE`: quick count of signature deficits (smaller is better).
- Sources: cover_match.c, d7hexr.c, kcopy_hub.c, regions.c (read them; headers explain the maths).
- Hexagon file format (hex/hex_q11.bin): int32 q, N, L; then L·(q+1) int32 point ids (the points of each line, line
  order = line id); then N·7 uint8 coordinates (points of the quadric X0X4+X1X5+X2X6 = X3² in PG(6,11)).

## Machine rules (shared 4 cores / 15 GB with Opus and 7 other cards)
THREADS=1 everywhere; prefix heavy commands with `timeout 900 nice -n 10`; at most ONE heavy process at a time;
≤ 1.5 GB memory; total time box about 20 minutes of work.

## Report
Append ONE line of JSON to `research/squads/c157-r2/scoreboard.jsonl`:
`{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command>", "score": <number>,
"valid": true|false, "next": "<one line>"}` (score as defined in your card), then reply in at most 5 lines.

## New since round 1 (read this)
- Round 1 results: research/squads/LOG.md (entry "cell-15-7 ... round 1") and research/squads/c157-r1/scoreboard.jsonl.
- `research/squads/c157-r1/c6/cover_match2` (same arguments as cover_match) uses exact candidate lists and gives much
  better starts (K = 16 leftover 3,403; K = 20 9,027; K = 24 20,037). The leftovers are true Hall violations.
- d7hexr now has env `CKPT=file` (writes the current solution whenever the proxy reaches a new low below 2000, at most
  every 20 s) and `NOTRUE=1` (no early stop on the 3-copy BFS: it runs until proxy 0, which is valid for 3, 5 and 7
  copies alike). It also writes DONE.sol when it times out unsolved.
- `kcopy_hub checkf HEX SOL 3` BFSes only the freed sources (hubs reach everything whatever M is) and prints far
  pairs per source; much faster than `check`.
- The real 7-copy graph has some routes the proxy ignores, but an uncovered proxy target is truly covered in all three
  copies only ~6 % of the time, so proxy 0 is the right goal.
- c4's hub graphs: research/squads/c157-r1/c4/hgK.hg for K = 9..51.
