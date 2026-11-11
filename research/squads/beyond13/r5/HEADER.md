# beyond-d13 squad, round 5: shared header (read all of it before your card)

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
- At most 0.5 GB per process this round (the director holds 11-13 GB): haar_big0 needs about N/2 bytes, haarcheck_gen 0.75 N bytes, hmeta about 0.6 N bytes.
- No git commands. Write only inside your card folder research/squads/beyond13/r5/<card>/ (outputs, code, solutions).
- Time box: about 25 minutes, then report.

- NEW in round 5: `$B/bin/haar_sym` — haar_gen3 plus alpha-orbit search (ORBIT="k m f") on its group families, including
  metacyclic groups with alpha = scaling (a,j) -> (u a, j) (automatic, or AMU=u). Header: research/structured/haar_sym.c.
- `python3 $B/metacheck.py SOL` — independent checker for Haar graphs of metacyclic groups (haar_gen3 / haar_sym
  solution files "d D meta m k r n NC N .."; prints VALID / INVALID). Use it on every meta find (N <= 2e7: < 1 min).
  For tables (exh3 / other groups): `python3 $B/tab2edges.py TABLE.bin OUT.edges s1 s2 ...` then `$B/bin/apsp OUT.edges d D`.
- research/squads/beyond13/r1/c05/orbscan.c — exhaustive scan of S = {e, x, ax, a^2x} over all x (Δ = 4) for
  SL/PSL(2,p) x Z_n, exact cost, validated against haar_big0 and haarcheck_gen.

- NEW in round 5: `$B/meta/hmeta` — fast metacyclic Haar search (bit-parallel BFS, ~14 evaluations/s at N = 2e7 on one
  core; random S plus targeted moves). `THREADS=1 $B/meta/hmeta d D seconds seed K OUT m k r` (env START=<sol>, EVAL=<sol>,
  TARGP). Solution files are haar_gen3 format (check with metacheck.py). Group picker: `python3 $B/meta/mpick.py d D Nlo Nhi [k,..]`
  (odd-order Frobenius groups Z_m x|_r Z_k, m prime = 1 mod k).
- `$B/bin/lift BASE n D seconds seed OUTPREFIX [T0 T1 L]` — cyclic (Z_n) voltage lifts of a small base graph,
  annealed voltages (squad r2/e16's lift.c; bases in $B/lifts/bases/, format "nverts" then "u v" lines; START=file).
  Writes OUTPREFIX.edges when cost 0. Check lifts with `$B/bin/apsp EDGES d D` (all pairs).
- `DEG=4 $B/bin/liftd ...` — the same lift annealer for DEG-regular bipartite bases (any degree <= 8; source
  $B/lifts/liftd.c; base K4,4 in $B/lifts/bases/k44.txt).
- `python3 $B/metacheck2.py SOL` checks products of metacyclic groups (haar_gen3 "prod meta .. meta ..").

## Values after rounds 1-4 (all checked) — the values to beat

| cell | value | how | near misses (cost) |
|---|---|---|---|
| (3,13) | **3,200** | Z160 lift of GP(10,3) | Z33 x|_4 Z5 voltages on GP(10,3) at 3,300 (2); Tutte 8-cage n = 107 (10) |
| (3,14) | **5,600** | Z280 lift of GP(10,3) | GP(10,3) n = 282 (2); Pappus n = 312, 5,616 (2); Tutte 8-cage n = 187, 5,610 (2) |
| (4,13) | **186,314** | odd-order Z4903 x|_230 Z19, random S | Z3307 x|_265 Z29 (N 95,903) and Z2297 x|_1862 Z41 (N 94,177): 2 |
| (4,14) | **490,070** | odd-order Z7001 x|_4532 Z35, random S, hmeta (r4/g13: T0=4 T1=0.5 REHEAT=200 closed cost 1 -> 0) | Z12959 x|_3582 Z19 (N 246k): 3 |
| (5,13) | **3,525,298** | (Z29 x|_16 Z7) x (Z457 x|_289 Z19), random S | (29x7)x(677x13) N 1.787M: 2-4 |
| (5,14) | **12,352,392** | PSL(2,53) x Z83, random S | PSL(2,67) x Z41: 1 |
| (6,13) | **41,734,392** | PSL(2,83) x Z73 "3 2 0" | SL(2,59) x Z103 (N 21.15M): 2; PSL(2,67) x Z139: 3 |
| (6,14) | **187,990,656** | SL(2,97) x Z103 "3 2 0" (RANDORB screen then 2 links) | SL(2,67) x Z313: 4 |
| (7,13) | **312,227,760** | SL(2,229) x Z13 "3 2 1" | SL(2,137) x Z61: 6; SL(2,541): 4-6 |
| (7,14) | 1,673,976,240 | SL(2,269) x Z43 "3 2 1" (r4/g06; director check pending) | PSL(2,277) x Z79: 1 |
| (4,11) | **27,554** | odd-order Z599 x|_498 Z23 (raised from 24,360) | |
| (5,11) | **299,222** | odd-order (Z29 x|_7 Z7) x (Z67 x|_9 Z11) (raised from 297,648) | |
| lab values at D = 11, 12 | (3,11) 1,474, (3,12) 2,176, (4,12) 68,544, (5,12) 1,041,768, (6,11) 2,094,960 | research/frontier/beyond/BEYOND_TABLE.md | |

## Already ruled out (do not repeat)

- Orbit S on metacyclic groups; metacyclic k <= 8; lifts at Δ = 4, 5 (K4,4, PG(2,3), GQ(3,3), biplane, random bases:
  all below the Haar values); 40-vertex cubic bases at (3,13).
- lift.c cools over L evaluations (default 20000): short runs never cool. Use L = 300-1500 for 20-100 s runs (r4/g01).
- From D = 11/12: k = 2, 4, 5, 6 orbits, self-dual S, tuning knobs, fixed-generator moves, -I as generator, composite n.
- MEMORY: cap 0.5 GB per process; python metacheck only for N <= 2e6.

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond13/r5/scoreboard.jsonl:
`{"card":"hNN","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution or edge file>",
"best_cost":<lowest cost if nothing solved>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
