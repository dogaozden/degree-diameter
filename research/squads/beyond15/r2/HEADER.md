# beyond-d15 squad, round 2: shared header (read all of it before your card)

Job beyond-d15 (Opus director, 2026-11-01, branch claude/new-cells-d15-d16-fpj633). Bipartite degree-diameter problem:
the largest bipartite graph with maximum degree Δ and diameter at most D. Goal: FIRST values for the new cells D = 15
and D = 16 at Δ = 3..6. Nothing is recorded there yet, so every checked graph is a first value; bigger is better.
Size cap: 20 billion vertices. Your card names one cell (or two) and one idea. Run that idea, not something else.

## Tools (already built). F=/home/user/degree-diameter/research/frontier

- `$F/bin/hmeta` — fast Haar search over metacyclic groups G = Z_m x|_r Z_k (r^k = 1 mod m), random S, bit-parallel BFS.
  `env T0=8 T1=1 REHEAT=400 THREADS=1 $F/bin/hmeta d D seconds seed 8 OUT m k r`; env START=<file> continues from a
  saved S (OUT.best); EVAL=<file> prints the cost of a saved S. Prints `RESULT ... best=<cost>`; cost 0 = diameter <= D,
  solution written to OUT (haar_gen3 format). Speed (one core): N = 6.6e5: ~650 evals/s; N = 2.3e7: ~17 evals/s;
  N = 8.7e7: ~4 evals/s. Memory ~0.6 N bytes. Header: $F/beyond13/meta/hmeta.c (first 30 lines).
- `python3 $F/beyond13/meta/mpick.py d D Nlo Nhi k1,k2,..` — odd-order Frobenius groups Z_m x|_r Z_k (m prime = 1 mod k,
  k odd prime, r of order k), prints "m k r N mu". `python3 $F/beyond13/meta/enumeta.py` lists all metacyclic groups
  in an order range (read its first lines for usage).
- `$F/bin/haar_gen3` — Haar search over many families (meta, agl1, sl/psl/pgl over prime powers, prod G1 G2), random S,
  odd D supported. Header: $F/haar_gen3.c (first 40 lines). Products of two Frobenius groups won (5,13).
- `$F/bin/haar_big0` — SL(2,p) x Z_n / PSL(2,p) x Z_n with S closed under an automorphism alpha of order 3:
  `ORBIT="k m f" THREADS=1 $F/bin/haar_big0 d D seconds seed 8 OUT sl|psl p n` (d = f + 3m; Δ=4 "3 1 1", Δ=5 "3 1 2",
  Δ=6 "3 2 0"); picker `python3 $F/beyond11/pick.py d D mu_lo mu_hi 3 maxn`. Memory N/2 bytes. Header: $F/beyond11/haar_big0.c.
- `$F/bin/haar_sym` — haar_gen3 plus alpha-orbit S (research/structured/haar_sym.c).
- `$F/bin/lift BASE n D seconds seed OUTPREFIX T0 T1 L` — cyclic Z_n voltage lifts of a small bipartite cubic base
  (anneal; use T0=2.0 T1=0.05 L=1200 for short runs; START=<voltages file>). Writes OUTPREFIX.best, and OUTPREFIX.edges
  when cost 0. Bases: $F/beyond13/lifts/bases/*.txt (format: number of vertices, then "u v" lines; sides must be
  0..h-1 and h..2h-1, see $F/beyond13/lifts/lift.c lines 1-5).
- `$F/bin/scan BASE n D seconds seed OUTPREFIX 6` (env START=<voltages>) — exhaustive 1-opt voltage scan + tabu walk;
  the lift finisher that closed the D = 13, 14 cubic cells. `DEG=4 $F/bin/liftd ...` — the lift annealer for any degree.
- `$F/bin/exh3` — exhaustive cubic Haar pairs over a group table ($F/beyond/cubic/exh3.c; $F/beyond/cubic/sweep_meta.py).
- Lift bound (exact upper bound on n for Z_n lifts of a base): research/squads/beyond13/r4/g11 on branch
  origin/claude/beyond-d13-search-z35z61 (`git show origin/claude/beyond-d13-search-z35z61:research/squads/beyond13/r4/g11/lbound.c`).
- Size law: mu = N exp(-W/N) = expected holes of a random S (W = words of length <= D-1 per side). Each card's group
  pickers print mu. Higher mu = bigger graph = harder. Past jobs: mu ~3 solves in a few evaluations, ~10 in hundreds,
  ~15-25 with chained links at small Δ (cheap evaluations).

## Checkers (every reported find must pass one)

- `$F/bin/apsp EDGES d D` (all pairs; edge lists up to ~5e5 vertices; first line n, then "u v").
- `python3 $F/beyond13/metacheck.py SOL` (metacyclic, N <= 2e6 only in this round: memory) and `metacheck2.py` (products).
- `$F/bin/haarcheck_gen SOL` (SL/PSL x Z_n; ~1 min per 2e7 elements). Larger finds: report the file; the director checks.

## Machine rules (4 cores, 15 GB, shared by 16 cards and the director's billion-vertex searches)

- THREADS=1 always. Prefix every heavy command with `timeout 105 nice -n 10`.
- **Every Bash command must finish in under 110 s** (a longer one goes to the background and you sit idle). Use
  seconds <= 100 and chain links with START=<OUT>.best; change the seed between links. Put START in front with `env`.
- At most 0.5 GB per process. No git commands. No remote-session or scheduling tools. Never kill processes you did
  not start (no pkill -f on shared names).
- Write only inside your card folder research/squads/beyond15/r2/<card>/ (code, outputs, solutions).
- Time box: about 25 minutes of work, then write the scoreboard line and report.

## Values so far (all checked; beat them in your cell)

| cell | value | construction | mu (Haar) |
|---|---:|---|---|
| (3,15) | 10,746 | symmetric Z199 lift of the Gray graph (order-9 rotation, lambda = 43), director, liftsym exhaustive | 12.1 |
| (3,16) | 17,602 | Haar graph of Z677 x|_362 Z13, S = {e,(153,9),(562,10)} (r1/a04, hmeta d = 3) | 5.1 |
| (4,15) | 1,343,054 | Haar graph of Z9199 x|_8708 Z73 (r1/b01, hmeta, 21 s) | 15.4 |
| (4,16) | 3,517,286 | Haar graph of Z24091 x|_1680 Z73 (director, hmeta, 48 s) | 8.5 |
| (5,15) | 46,787,954 | Haar graph of Z154927 x|_147000 Z151 (director, hmeta, 35 s) | 5.3 |
| (5,16) | 167,009,842 | Haar graph of Z272003 x|_231904 Z307 (r1/c02, hmeta) | 3.0 |
| (6,15) | 867,831,360 | SL(2,241) x Z31, 2 free alpha-orbits (director; check pending) | 10.0 |
| (6,16) | 4,021,844,904 | PSL(2,307) x Z139, 2 free alpha-orbits (director; check pending) | 11.6 |

## NEW tool: symmetric voltage lifts (director, this job)

- `$F/bin/liftsym BASE PERM n lambda D seconds seed OUTPREFIX` — Z_n lifts whose voltages are equivariant under a base
  automorphism rho (PERM file) with multiplier lambda (lambda^k = 1 mod n, k = order of rho): x_{rho(e)} = lambda x_e.
  Z_n x|_lambda Z_k then acts on the lift with b/k vertex orbits, and only one voltage per rho-orbit of edges is free.
  Anneal + built-in exhaustive 1-opt sweeps (any n). env EXH=1: exhaustive over ALL gauge classes (n prime only; one
  run is seconds to minutes), START=<.best file> (voltages "e x", only orbit representatives are read), T0, T1, L.
  Writes OUTPREFIX.best, and OUTPREFIX.edges at cost 0 (check: `$F/bin/apsp EDGES 3 D`). Source and header:
  $F/beyond15/liftsym.c. Lambda of order dividing k: `python3 $F/beyond15/lsym/lam.py n k`.
- Bases with rotation automorphisms (lift format + .perm): $F/beyond15/lsym/{desargues, pappus, heawood, mobkan, nauru,
  f26a, dyck, tutte8, gray, foster}.txt/.perm (order of rho: 5, 3, 7, 8, 4, 13, 8, 5, 9, 15) and gray18, foster18
  (order 3 and 5: more vertex orbits, more free voltages). Make more with `python3 $F/beyond15/lsym/mklcf.py NAME "a1,..,ap" REPS [SHIFT]`
  (LCF notation, odd entries; SHIFT = a multiple of the period p, even; prints girth and orbit counts).
- `python3 $F/beyond15/lsym/sweep.py BASE D nlo nhi [maxlam] [timeout]`: EXH over every prime n in a range.
- `python3 $F/beyond15/lsym/haarsweep.py D Nlo Nhi klo khi`: exhaustive sweep of CUBIC Haar graphs of metacyclic groups
  Z_n x|_lambda Z_k (each (k, j-pattern {0,a,b}, n, lambda) is a single graph up to isomorphism after gauge fixing).
- `$F/bin/metacheck SOL` — the director's independent C checker for metacyclic groups and products (any N up to ~1e9;
  ~1 min per 2e7 elements per thread). Use it instead of metacheck.py for N > 2e6 (`OMP_NUM_THREADS=1`).

## Already known or ruled out (do not repeat)

- Round 1 negatives: SL/PSL(2,p) x Z_n with alpha-orbit S at Δ = 4 ("3 1 1", floor cost 192) and Δ = 5 ("3 1 2", floor 65;
  "5 1 0" floor 52 and the annealer hangs at m = 1, f = 0); products of two Frobenius groups at (4,15) and (5,15) (cost 4,
  below single metacyclic groups); AGL(1,q); composite-m metacyclic groups at (4,16) (not fixed-point-free, cost ~9e5);
  plain Z_n lifts of GP(10,3) at (3,15) (cost 6 at n = 500); Z_a x Z_b lifts of GP(10,3) (8,400); a plain Z330 lift of
  the Tutte 8-cage (9,900); (6,15) SL(2,151) x Z127 at mu 11.6 (cost 18 under load).
- k-threshold (r1/c05, research/squads/beyond15/r1/c05/KTABLE.md): metacyclic groups behave like random groups from
  k ~ 31 (D = 15) and k ~ 43 (D = 16) at Δ = 4; at Δ = 5 the cost still falls with k up to 97+ (k = 151-307 used).
- Δ = 3, director (do NOT repeat): exhaustive symmetric lifts of Desargues (order 5, all prime n 401-1000), Gray
  (order 9, prime n 190-400), Tutte 8-cage (order 5, prime n 330-440), Foster (order 15, prime n 200-250; n = 211 has
  min cost 2 at 18,990); exhaustive cubic metacyclic Haar sweep for k = 7..40 at both D (haarsweep.py).
- Older (D = 13, 14): orbit S inside metacyclic groups saturates; lifts at Δ = 4, 5 of K4,4, PG(2,3), GQ(3,3), biplane
  and random bases stayed below the Haar values; non-abelian voltage groups on GP(10,3) were worse.
- At odd D, PSL(2,p) with n = 1 is the worst shape (involutions are the holes); odd-order groups avoid special holes.

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond15/r2/scoreboard.jsonl:
`{"card":"<id>","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution or edge file>",
"best_cost":<lowest cost if nothing solved>,"mu":<mu of the best run>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
