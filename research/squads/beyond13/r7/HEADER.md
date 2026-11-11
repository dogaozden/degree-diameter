# beyond-d13 squad, round 7: shared header (read all of it before your card)

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
- No git commands. Write only inside your card folder research/squads/beyond13/r7/<card>/ (outputs, code, solutions).
- Time box: about 25 minutes, then report.

- NEW in round 7: `$B/bin/haar_sym` — haar_gen3 plus alpha-orbit search (ORBIT="k m f") on its group families, including
  metacyclic groups with alpha = scaling (a,j) -> (u a, j) (automatic, or AMU=u). Header: research/structured/haar_sym.c.
- `python3 $B/metacheck.py SOL` — independent checker for Haar graphs of metacyclic groups (haar_gen3 / haar_sym
  solution files "d D meta m k r n NC N .."; prints VALID / INVALID). Use it on every meta find (N <= 2e7: < 1 min).
  For tables (exh3 / other groups): `python3 $B/tab2edges.py TABLE.bin OUT.edges s1 s2 ...` then `$B/bin/apsp OUT.edges d D`.
- research/squads/beyond13/r1/c05/orbscan.c — exhaustive scan of S = {e, x, ax, a^2x} over all x (Δ = 4) for
  SL/PSL(2,p) x Z_n, exact cost, validated against haar_big0 and haarcheck_gen.

- NEW in round 7: `$B/meta/hmeta` — fast metacyclic Haar search (bit-parallel BFS, ~14 evaluations/s at N = 2e7 on one
  core; random S plus targeted moves). `THREADS=1 $B/meta/hmeta d D seconds seed K OUT m k r` (env START=<sol>, EVAL=<sol>,
  TARGP). Solution files are haar_gen3 format (check with metacheck.py). Group picker: `python3 $B/meta/mpick.py d D Nlo Nhi [k,..]`
  (odd-order Frobenius groups Z_m x|_r Z_k, m prime = 1 mod k).
- `$B/bin/lift BASE n D seconds seed OUTPREFIX [T0 T1 L]` — cyclic (Z_n) voltage lifts of a small base graph,
  annealed voltages (squad r2/e16's lift.c; bases in $B/lifts/bases/, format "nverts" then "u v" lines; START=file).
  Writes OUTPREFIX.edges when cost 0. Check lifts with `$B/bin/apsp EDGES d D` (all pairs).
- `DEG=4 $B/bin/liftd ...` — the same lift annealer for DEG-regular bipartite bases (any degree <= 8; source
  $B/lifts/liftd.c; base K4,4 in $B/lifts/bases/k44.txt).
- `python3 $B/metacheck2.py SOL` checks products of metacyclic groups (haar_gen3 "prod meta .. meta ..").

- NEW: `$B/bin/scan BASE n D seconds seed OUT 6` (env START=<voltages>) — squad r5/h02's lift finisher: exhaustive
  1-opt voltage scan with early-abort BFS and a tabu plateau walk; it closed a cost-2 lift near miss in 7 iterations.

## The rule this round tests, and the values to beat

Rule found this job: at small Δ (4, 5, and at D = 11 also 6), Haar graphs of metacyclic groups Z_m x|_r Z_k (k >= 13,
odd order preferred at odd D) with RANDOM S beat the SL/PSL(2,p) x Z_n alpha-orbit values. Fast tool: hmeta
(`env T0=8 T1=1 REHEAT=400 THREADS=1 $B/meta/hmeta d D secs seed 8 OUT m k r`, START=<best> to chain; any m, k, r with
r^k = 1 mod m; mpick.py lists prime-m Frobenius groups; composite m gives more orders). Check: metacheck.py (and apsp
below 5e5 vertices). NOTE (bash): put START in front with `env`, never as `${S:+START=$S}` (that breaks the command).

| cell | value to beat | source | note |
|---|---|---|---|
| (4,8) | 2,184 | 2013 table | |
| (4,9) | 4,970 | 2013 table | Z101 x|_5 Z25 (5,050) cost 2 (r6/i09) |
| (4,10) | 11,748 | 2013 table | Z109 x|_12 Z54 (11,772) cost 2 (r6/i09 + director) |
| (5,8) | 9,760 | lab (harvest) | |
| (5,9) | 29,756 | lab (harvest, metacyclic 346 x 43) | r6/i10: Z1093 x|_901 Z13 28,418 |
| (5,10) | 90,886 | this job (r6/i10, Z1567 x|_871 Z29); 2013 value 90,068 | Z2687 x|_2416 Z17 and Z3511 x|_722 Z13 at cost 1 (director chains running) |
| (6,9) | 121,440 | lab (lab/ledger.jsonl) | |
| (6,10) | 506,160 | lab (lab/ledger.jsonl) | |
| (6,11) | 2,098,766 | this job (r6/i11, Z17203 x|_9845 Z61) | Z36251 x|_19639 Z29 at 2 |
| (6,12) | 9,366,240 | lab | |
| (6,13) | 41,734,392 | this job (PSL(2,83) x Z73) | director chains on k = 37, 41, 43 running |
| (7,9), (7,10), (7,11), (7,12) | look up: research/frontier/TABLE.md, `git log --oneline origin/master | grep 'Δ7·D9'` etc., research/frontier/beyond/BEYOND_TABLE.md | | (7,10) 2,298,240; (7,11) 11,012,976; (7,12) 59,838,504 |
| (4,12), (4,13), (4,14) | 74,066; 192,382; 497,042 | this job | (4,13) Z2069 x|_2064 Z47 (194,486) cost 2 |
| (5,13), (5,14) | 3,594,910; 12,776,064 | this job | |
| (3,13), (3,14) | 3,400; 5,640 | this job (lifts of GP(10,3); lift + scan) | |

## Already ruled out (do not repeat)

- Orbit S on metacyclic groups; metacyclic k <= 3 (k = 5, 7 weak); lifts at Δ = 4, 5; lifts at D = 11, 12 (Δ = 3).
- MEMORY: cap 0.5 GB per process; python metacheck only for N <= 2e6. No remote-session tools, no pkill -f on shared paths.

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond13/r7/scoreboard.jsonl:
`{"card":"jNN","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution or edge file>",
"best_cost":<lowest cost if nothing solved>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
