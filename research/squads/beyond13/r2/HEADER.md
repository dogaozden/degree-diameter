# beyond-d13 squad, round 2: shared header (read all of it before your card)

Job beyond-d13 (Opus director, 2026-11-01). Bipartite degree-diameter problem: the largest bipartite graph with maximum
degree Δ and diameter at most D. Goal: FIRST values for the new cells D = 13 at Δ = 3..10 and D = 14 at Δ = 3..8. Nothing
is recorded there yet, so any checked graph is a first value; bigger is better. Size cap: 20 billion vertices.

## Tools (already built; B=/home/user/degree-diameter/research/frontier/beyond13)

- `$B/bin/haar_big0` — Haar graph H(G,S), G = SL(2,p) x Z_n or PSL(2,p) x Z_n (p prime >= 5; n = 1 or a prime = 1 mod 3;
  gcd(p,n) = 1), S closed under alpha (order 3). Header comment: research/frontier/beyond11/haar_big0.c (first 60 lines).
  `ORBIT="k m f" THREADS=1 $B/bin/haar_big0 d D seconds seed K OUTFILE sl|psl p n`
  d = f + 3m. "3 m 1": S = {e} + m alpha-orbits of size 3; "3 m 2": plus one random fixed generator (drawn from the seed,
  never moved); "3 m 0": m free orbits without e (use when 3 | d). Standard per Δ: 3:"3 1 0" 4:"3 1 1" 5:"3 1 2"
  6:"3 2 0" 7:"3 2 1" 8:"3 2 2". Output line `RESULT ... best=<cost> evals=..` (cost 0 = diameter <= D, solution
  written to OUTFILE; OUTFILE.best holds the best S so far; with f = 0 also OUTFILE.orb).
  Env: START=<file> (continue from a saved S: OUTFILE.best, or OUTFILE.orb / OUTFILE.best.orb when f = 0),
  RANDORB=m (cost statistics of m random symmetric S, no search), EVAL=<file> (cost of a saved S), UNCPRINT=1 (with
  EVAL: list up to 200 uncovered elements as "idx mat(a,b,c,d) z=Z"), K (candidates per step, default 8 in our runs).
- `$B/bin/haar_gen3` — Haar search over many other groups (meta m k r, agl1 q, sl/psl/pgl q for prime powers, prod G G),
  random S (no orbits), odd D supported. Header: research/frontier/haar_gen3.c (first 40 lines).
- `$B/bin/haarcheck_gen SOL` — the independent checker (prints VALID / INVALID; memory 0.75 N bytes; ~1 min per 2e7
  group elements on one thread). Use it on every solution file you report: `timeout 105 nice -n 10 $B/bin/haarcheck_gen SOL > SOL.gen.txt`.
  If N > 3e7 the check needs more than 110 s: run it with `nohup nice -n 10 $B/bin/haarcheck_gen SOL > SOL.gen.txt 2>&1 &`
  and poll with short commands. If N > 2e8, do not check it yourself; report it and the director checks it.
- `$B/bin/exh3`, `$B/bin/apsp` — exhaustive cubic Haar pairs over a group table; all-pairs diameter check of an edge list
  (research/frontier/beyond/cubic/exh3.c, research/lifts/coordinator_check/apsp.c).
- `python3 $B/pick.py d D mu_lo mu_hi [k=3] [maxn]` — SL/PSL(2,p) x Z_n with size-law mu in range, sorted by N.
  mu = N exp(-W/N) ~ expected holes of a random S. At D = 11/12 mu 2-5 solved in tens of evaluations, mu ~7 in ~300,
  mu ~10 in ~1,000.

## Machine rules (4 cores, 15 GB shared with the director's 20-billion-vertex check, 7.5 GB)

- THREADS=1 always. Prefix every heavy command with `timeout 105 nice -n 10`.
- **Every Bash command must finish in under 110 s** (a longer one goes to the background and you sit idle). Use
  haar_big0 seconds <= 100 and chain runs with START=<OUTFILE>.best (or .orb for f = 0); change the seed between links.
- At most 1.5 GB per process: haar_big0 needs about N/2 bytes, haarcheck_gen 0.75 N bytes.
- No git commands. Write only inside your card folder research/squads/beyond13/r2/<card>/ (outputs, code, solutions).
- Time box: about 25 minutes, then report.

- NEW in round 2: `$B/bin/haar_sym` — haar_gen3 plus alpha-orbit search (ORBIT="k m f") on its group families, including
  metacyclic groups with alpha = scaling (a,j) -> (u a, j) (automatic, or AMU=u). Header: research/structured/haar_sym.c.
- NEW: `python3 $B/metacheck.py SOL` — independent checker for Haar graphs of metacyclic groups (haar_gen3 / haar_sym
  solution files "d D meta m k r n NC N .."; prints VALID / INVALID). Use it on every meta find (N <= 2e7: < 1 min).
  For tables (exh3 / other groups): `python3 $B/tab2edges.py TABLE.bin OUT.edges s1 s2 ...` then `$B/bin/apsp OUT.edges d D`.
- NEW: research/squads/beyond13/r1/c05/orbscan.c — exhaustive scan of S = {e, x, ax, a^2x} over all x (Δ = 4) for
  SL/PSL(2,p) x Z_n, exact cost, validated against haar_big0 and haarcheck_gen.

## Round 1 results (all checked unless marked) — the values to beat

| cell | value | how | size law 2N at mu 5 |
|---|---|---|---|
| (3,13) | 2,880 | A6 x Z4, exhaustive S = {e,x,y} (r1/c03 ex.c); also SL(2,11) 2,640, PSL(2,13) 2,184; metacyclic sweep (r1/c01, exh3, k 8-24) best Z133 x|_36 Z9 2,394 at N <= 1,200 (N 1,201-3,600 not reached: CPU starved) | 2,900 |
| (3,14) | none yet | (r1/c02 metacyclic sweep still running) | 5,200 |
| (4,13) | **186,314** | odd-order metacyclic Z4903 x|_230 Z19, random S (haar_gen3, r1/c15); k = 13, 17, 23 also solved at 170-180k; k = 3 hopeless, k = 11 stalls | 164,000 |
|  | 170,520 | PSL(2,29) x Z7, exhaustive orbit scan (r1/c05) | |
| (4,14) | 482,160 | PSL(2,41) x Z7 "3 1 1" (r1/c06); PSL(2,79) x Z1 (492,960) stuck at cost 31 | 447,000 |
| (5,13) | 3,217,056 | PSL(2,47) x Z31 "3 1 2" (r1/c07); PSL(2,37) x Z67 stuck at 18. Director: meta Z89491 x|_74121 Z19 (N = 1.70M) random S reached cost 4 in 25 s; meta with haar_sym orbits ("3 1 2") was bad (3,536) | 3,500,000 |
| (5,14) | 11,696,856 | PSL(2,227), random S (haar_gen3, r1/c08); the orbit form "3 1 2" stalls at 18 | 12,700,000 |
| (6,13) | 40,427,088 | PSL(2,103) x Z37 "3 2 0" (r1/c09); PSL(2,181) x Z7 (mu 8.5) stuck at 15, SL(2,83) x Z37 (mu 11.5) at 6 | 40,100,000 |
| (6,14) | 186,466,200 | PSL(2,101) x Z181 "3 2 0" (r1/c10); PSL(2,61) x Z823 (mu 7.5) at 78 | 183,000,000 |
| (7,13) | 299,455,200 | SL(2,199) x Z19 "3 2 1" (r1/c11); SL(2,281) x Z7 310,628,640 cost 0, check pending | 303,000,000 |
| (7,14) | 1,587,571,920 | SL(2,109) x Z613 "3 2 1" (r1/c12; director's check running) | 1,660,000,000 |
| (8,13) | 1,512,114,240 | SL(2,911) x Z1 "3 2 2" (r1/c13; director checks) | 1,700,000,000 |
| (8,14), (9,13), (10,13) | 10.74e9, 7.51e9, 19.98e9 | director (checks running) — not card cells | |

## Already ruled out (do not repeat)

- Odd D rule (beyond-d11 and r1/c14 ANATOMY at (5,13)): involutions and central elements are the hard holes; -I in SL
  is missed by 20-46 % of random S; central elements (+-I, z) cost ~n e^(-λ/6); PSL involutions cost 5-11 holes per S.
  An odd-order group has NO involutions — that is why the metacyclic groups of odd order won (4,13).
- k = 3 metacyclic (virtually abelian) is hopeless; k = 2, 4, 5, 6 orbits, self-dual S, K/TARGP tuning, fixed-generator
  moves, -I as a generator, composite n, near-miss finisher (all at D = 11/12, beyond-d11).
- Small p with huge n (p <= 23, n >= 600) is bad for the SL/PSL orbit search (r1/c06, c07, c10).
- Floors: a D = 13 value must beat the D = 12 value ((3,12) 2,176, (4,12) 68,544, (5,12) 1,041,768, (6,12) 9,366,240,
  (7,12) 59,838,504, (8,12) 284,095,056); a D = 14 value must beat the D = 13 value at the same Δ.

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond13/r2/scoreboard.jsonl:
`{"card":"eNN","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution file>",
"best_cost":<lowest cost if nothing solved>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
