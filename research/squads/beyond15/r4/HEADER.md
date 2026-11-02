# beyond-d15 squad, round 4: shared header (read all of it before your card)

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
- Write only inside your card folder research/squads/beyond15/r4/<card>/ (code, outputs, solutions).
- Time box: about 25 minutes of work, then write the scoreboard line and report.

## Values so far (all checked; beat them in your cell)

| cell | value | construction | mu (Haar) |
|---|---:|---|---|
| (3,15) | 11,802 | Z281 x|_59 Z7 acting with 6 orbits: symmetric lift of a Z7 cover of the Tutte-8-cage/Foster quotient (r3/k03, EXH) | |
| (3,16) | 20,466 | symmetric Z379 lift of the Gray graph (order-9 rotation, lambda 84; director, exhaustive) | |
| (4,15) | 1,343,054 | Haar graph of Z9199 x|_8708 Z73 (r1/b01) | 15.4 |
| (4,16) | 3,623,866 | Haar graph of Z24821 x|_16022 Z73 (r2/f02) | 12.6 |
| (5,15) | 47,587,354 | Haar graph of Z76507 x|_75438 Z311 (r3/m04) | 7.0 |
| (5,16) | 172,011,046 | Haar graph of Z569573 x|_342015 Z151 (r3/m01 closed r1/c02's cost-2 state) | 6.2 |
| (6,15) | 867,831,360 | SL(2,241) x Z31, 2 free alpha-orbits (director) | 10.0 |
| (6,16) | 4,021,844,904 | PSL(2,307) x Z139, 2 free alpha-orbits (director) | 11.6 |

Lesson of round 2: two of the three Haar raises came from CLOSING a saved cost-2 state with a new seed (one short
hmeta link). If you reach cost <= 2, save the state and give it several new-seed links before moving on.

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
- `python3 $F/beyond15/lsym/quotgen.py D Vlo Vhi klo khi "tA tB a-b,a-b,..." [maxpat] [seed] [maxlam]`: symmetric lifts
  over ANY quotient multigraph (the quotient of the graph by the whole group Z_n x| Z_k; tA, tB orbits per side). Random
  Z_k patterns on the non-tree quotient edges, covers checked connected and simple, then EXH for prime n, or with env
  ANNEAL=<secs> an anneal of that many seconds for every n (composite too). Vlo, Vhi are vertex counts. Quotients:
  Gray "3 3 0-0,0-2,0-2,1-0,1-0,1-1,2-1,2-1,2-2"; t = 4 (Desargues shape) "2 2 0-0,0-1,0-1,1-0,1-0,1-1"; t = 2 (Haar) "1 1 0-0,0-0,0-0".
  The Tutte 8-cage quotient: derive it from lsym/tutte8.txt + tutte8.perm (orbits of the perm, edges between orbits).
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

- Round 2 negatives: Gray order-3 family (gray18) at n = 331-397 (cost 56-78 per orbit, far); Foster order-5 family
  (foster18) at n >= 198 (cost 6 at best, rising with n); Foster order-15 at D = 15 (n = 151: min 50); lambda of
  non-maximal order on Gray (cost 102); Dyck and Nauru symmetric lifts (cost > 1,000); GQ(3,3) quartic symmetric lifts
  at (4,15) (cost 184); even-order metacyclic groups at (4,16) (cost 33); Frobenius k = 151-211 at (4,16) (cost 1-10);
  exhaustive cubic metacyclic Haar sweep k = 41..120 (r2/e04: best 11,342 at D = 15, 19,306 at D = 16); Tutte 12-cage
  symmetric lifts reached 17,892 at (3,16) and 10,836 at (3,15) (r2/e05).
- Round 3 negatives: Tutte 8-cage at n = 394-420 and n = 683-701 (k01; n = 403 stays at cost 2); Gray order-9 at composite
  n 380-418 (k02: cost 2 at n = 381, 399, director is closing them); composite-m cubic metacyclic Haar graphs (k05: cost 263+);
  Tutte 12-cage n = 143-175 (k06: cost 32+); 4-orbit quotient with composite n (k07: cost 10); (4,15) k = 31-59 (l03:
  Z11447 x| Z59 cost 2, director closing), k = 37-137 (l01: Z12721 x| Z53 cost 4); (4,16) k = 61-83 (l02: Z27337 x| Z67
  cost 2, director closing), k = 107-127 (l04: cost 2-4); (5,15) k = 137-163 (m02: closed Z171799 x| Z137 = 47,072,926, below).
- Director, in progress (do not repeat): closers on (4,15) Z11447 x| Z59, (4,16) Z27337 x| Z67, (5,16) Z283669 x| Z307,
  (3,16) Gray order-9 n = 381 (lambda 22) and n = 399 (lambda 4); anneals of the Gray-shape quotient k = 13, pattern
  [8,8,4,11], n = 158 at D = 15 (r3/k04's cost-2 near miss); EXH sweeps of the Tutte/Foster quotient shape over prime n
  (D = 15: k 5-14, 8 patterns each; D = 16: k 7-14, 4 patterns each).
- Machine: the scheduler gives every process group an equal share (autogroups), so `nice` has no effect; keep
  THREADS=1 and one heavy process at a time.

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond15/r4/scoreboard.jsonl:
`{"card":"<id>","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution or edge file>",
"best_cost":<lowest cost if nothing solved>,"mu":<mu of the best run>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
