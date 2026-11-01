# beyond-d13 squad, round 4: shared header (read all of it before your card)

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
- No git commands. Write only inside your card folder research/squads/beyond13/r4/<card>/ (outputs, code, solutions).
- Time box: about 25 minutes, then report.

- NEW in round 4: `$B/bin/haar_sym` — haar_gen3 plus alpha-orbit search (ORBIT="k m f") on its group families, including
  metacyclic groups with alpha = scaling (a,j) -> (u a, j) (automatic, or AMU=u). Header: research/structured/haar_sym.c.
- `python3 $B/metacheck.py SOL` — independent checker for Haar graphs of metacyclic groups (haar_gen3 / haar_sym
  solution files "d D meta m k r n NC N .."; prints VALID / INVALID). Use it on every meta find (N <= 2e7: < 1 min).
  For tables (exh3 / other groups): `python3 $B/tab2edges.py TABLE.bin OUT.edges s1 s2 ...` then `$B/bin/apsp OUT.edges d D`.
- research/squads/beyond13/r1/c05/orbscan.c — exhaustive scan of S = {e, x, ax, a^2x} over all x (Δ = 4) for
  SL/PSL(2,p) x Z_n, exact cost, validated against haar_big0 and haarcheck_gen.

- NEW in round 4: `$B/meta/hmeta` — fast metacyclic Haar search (bit-parallel BFS, ~14 evaluations/s at N = 2e7 on one
  core; random S plus targeted moves). `THREADS=1 $B/meta/hmeta d D seconds seed K OUT m k r` (env START=<sol>, EVAL=<sol>,
  TARGP). Solution files are haar_gen3 format (check with metacheck.py). Group picker: `python3 $B/meta/mpick.py d D Nlo Nhi [k,..]`
  (odd-order Frobenius groups Z_m x|_r Z_k, m prime = 1 mod k).
- `$B/bin/lift BASE n D seconds seed OUTPREFIX [T0 T1 L]` — cyclic (Z_n) voltage lifts of a small base graph,
  annealed voltages (squad r2/e16's lift.c; bases in $B/lifts/bases/, format "nverts" then "u v" lines; START=file).
  Writes OUTPREFIX.edges when cost 0. Check lifts with `$B/bin/apsp EDGES d D` (all pairs).
- `DEG=4 $B/bin/liftd ...` — the same lift annealer for DEG-regular bipartite bases (any degree <= 8; source
  $B/lifts/liftd.c; base K4,4 in $B/lifts/bases/k44.txt).
- `python3 $B/metacheck2.py SOL` checks products of metacyclic groups (haar_gen3 "prod meta .. meta ..").

## Values after rounds 1-3 (all checked unless marked) — the values to beat

| cell | value | how | notes |
|---|---|---|---|
| (3,13) | **3,200** | Z160 lift of the Desargues graph GP(10,3) (r2/e16) | 40-vertex bases at 3,240-3,360: cost >= 26 (r3/f01); metacyclic voltages on GP(10,3) (r3/f16 nlift.c): cost 2 at 3,300 |
| (3,14) | **5,600** | Z280 lift of GP(10,3) | n = 282 (5,640) cost 2, 281-285 cost 2-10 (r3/f02); 26 bases at 6,200: cost >= 20 |
| (4,13) | **186,314** | odd-order Frobenius Z4903 x|_230 Z19, random S (r1/c15) | lifts: PG(2,3) x Z4600 119,600 (r3/f04); GQ(3,3) lift at 192,000 cost 1,534 |
| (4,14) | **482,160** | PSL(2,41) x Z7 orbit S (r1/c06) | all SL/PSL groups at N 241-260k have mu 12-17 (r3/f09); GQ(3,3) x Z6100 lift (488,000) init cost 1,330 |
| (5,13) | **3,525,298** | odd-order (Z29 x|_16 Z7) x (Z457 x|_289 Z19), random S (r3/f08) | (29x7)x(677x13) N 1.787M cost 2-4; (23x11)x(547x13) cost 4 |
| (5,14) | **12,057,264** | PSL(2,73) x Z31, random S (r3/f10) | psl 37 x 233-241, psl 31 x 397, sl 31 x 199 stuck at 4-8 |
| (6,13) | **41,734,392** | PSL(2,83) x Z73 "3 2 0", mu 9.3 (r3/f11) | PSL(2,67) x Z139 (mu 9.5) cost 3 |
| (6,14) | **187,698,768** | PSL(2,137) x Z73 "3 2 0", mu 8.2 (r3/f12) | sl 97 x 103 cost 3 |
| (7,13) | **312,227,760** | SL(2,229) x Z13 "3 2 1" (r2/e10) | SL(2,541) x Z1 stuck at 10-12 |
| (7,14) | 1,671,605,424 | SL(2,163) x Z193 "3 2 1" (r3/f13; director check running) | SL(2,139) x Z313 (mu 6.7) cost 6, PSL(2,293) x Z67 cost 3 |
| (8,13) | **1,739,514,000** | SL(2,499) x Z7 "3 2 2", mu 7.5 (director) | |
| (4,11) | **27,554** | odd-order Z599 x|_498 Z23 (r3/f15) — raised from 24,360 | (5,11) 297,648 (SL(2,53)) not beaten: Z11467 x|_1429 Z13 cost 6 |
| (8,14), (9,13), (10,13) | 11.04e9, 7.51e9, 19.98e9 | director — not card cells | |

## Already ruled out (do not repeat)

- Orbit S on metacyclic groups (saturates); metacyclic k <= 8; metacyclic at even D (no clear gain).
- Δ = 5 lifts (K5,5, biplane, girth-6 bases) start at costs in the millions at 3.5M-11.8M (r3/f06).
- Lifts of K4,4 at Δ = 4 (cost 2e5 at 186k); 40-vertex cubic bases at (3,13).
- From D = 11/12: k = 2, 4, 5, 6 orbits, self-dual S, tuning knobs, fixed-generator moves, -I as generator, composite n.
- Floors: a D = 13 value must beat the D = 12 value; a D = 14 value must beat the D = 13 value at the same Δ.
- MEMORY: the director's 20-billion-vertex check was OOM-killed once at 12:35 (a python checker pushed the box over).
  Cap 0.5 GB per process, and run python metacheck only on N <= 2e6 (it needs ~100 bytes per element).

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond13/r4/scoreboard.jsonl:
`{"card":"gNN","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution or edge file>",
"best_cost":<lowest cost if nothing solved>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
