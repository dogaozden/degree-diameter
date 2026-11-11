# beyond-d15 squad, round 1: shared header (read all of it before your card)

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
- Write only inside your card folder research/squads/beyond15/r1/<card>/ (code, outputs, solutions).
- Time box: about 25 minutes of work, then write the scoreboard line and report.

## Director's values so far (all from 1-2 minute runs; beat them in your cell)

| cell | value | construction | mu |
|---|---:|---|---|
| (3,15) | none yet | GP(10,3) x Z500 (10,000) at cost 2 after a 90-s lift + 90-s scan | |
| (3,16) | none yet | GP(10,3) x Z900 (18,000) start cost 330 | |
| (4,15) | 1,324,798 | Z10859 x|_2950 Z61, hmeta, 28 s | 13.1 |
| (4,16) | none yet | Z30013 x|_10783 Z61 at cost 4 after 7 s | 14.4 |
| (5,15) | 46,787,954 | Z154927 x|_147000 Z151, hmeta, 35 s | 5.3 |
| (5,16) | none yet | Z576217 x|_512893 Z151 at cost 2 after 6 s | 6.2 |
| (6,15) | 843,134,880 | SL(2,281) x Z19, S = 2 free alpha-orbits | 5.8 |
| (6,16) | 4,021,844,904 | PSL(2,307) x Z139, S = 2 free alpha-orbits | 11.6 |

## Already known or ruled out (do not repeat)

- Metacyclic groups with SMALL k are nearly abelian at these diameters: Z1792337 x| Z13 at (5,15) stalled at cost 1,738
  where k = 151 solved in 35 s; k = 13 at (4,15) stalled at 58. Use k >= 61 unless your card says otherwise.
- From D = 13, 14 (job beyond-d13): orbit S inside metacyclic groups saturates; lifts at Δ = 4, 5 (K4,4, PG(2,3), GQ(3,3),
  biplane, random bases) stayed below the Haar values; non-abelian voltage groups on GP(10,3) were worse than Z_n;
  Haar graphs at Δ = 3 (A6 x Z4, PSL(2,7) x Z15) were below the Z_n lifts of GP(10,3) and Pappus.
- At odd D, PSL(2,p) with n = 1 is the worst shape (its ~p^2/2 involutions are the holes); odd-order groups and SL with
  small n avoid the special holes (research/frontier/beyond11/ODD_D_HOLES.md, research/frontier/beyond13/THEORY.md).

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond15/r1/scoreboard.jsonl:
`{"card":"<id>","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution or edge file>",
"best_cost":<lowest cost if nothing solved>,"mu":<mu of the best run>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
