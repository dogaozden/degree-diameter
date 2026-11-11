# beyond-d13 squad, round 1: shared header (read all of it before your card)

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
- No git commands. Write only inside your card folder research/squads/beyond13/r1/<card>/ (outputs, code, solutions).
- Time box: about 25 minutes, then report.

## Already found / already ruled out (do not repeat)

- (10,13) 19,980,294,768 PSL(2,503) x Z157 "3 3 1", first S at the cap (director; check running). Not a card cell.
- (9,13) and (8,14): director's runs. Not card cells.
- (4,14) 416,640 = SL(2,31) x Z7 "3 1 1", mu 2.15, 1 evaluation, VALID. Beat it.
- (5,13) 3,176,880 = SL(2,61) x Z7 "3 1 2", mu 1.22, 1 evaluation, VALID. Beat it.
- (4,13): SL(2,43) x Z1 "3 1 1", mu 3.5: stuck at cost 4 for 60 s (43k evaluations). No value yet.
- (5,14): PSL(2,227) x Z1 "3 1 2", mu 1.33: stuck at cost 18 for 60 s. No value yet (odd, since even D is usually easy).
- Odd D (research/frontier/beyond11/ODD_D_HOLES.md): at D = 2h+1 involutions are missed with probability ~exp(-λ/2) and
  central elements ~exp(-λ/h), λ = W/N (h = 6 at D = 13, worse than D = 11). -I in SL is central, an involution and
  alpha-fixed. Rule found at D = 11: SL(2,p) x Z_n with small n (1-43) and large p; PSL (p^2/2 involutions) was bad.
  At even D both families work.
- Tried at D = 11/12 with no gain: orbit orders k = 2, 4, 5, 6; self-dual (transpose-closed) S; K/TARGP/BOUNDCUR tuning;
  moving the fixed generator; -I as a generator; composite n; a meet-in-the-middle near-miss finisher.
- Floors (a D = 13 value must beat the D = 12 value): (3,12) 2,176, (4,12) 68,544, (5,12) 1,041,768, (6,12) 9,366,240,
  (7,12) 59,838,504, (8,12) 284,095,056. A D = 14 value must beat the D = 13 value at the same Δ.

## Scoreboard (one line per card, at the end)

Append ONE line of JSON to research/squads/beyond13/r1/scoreboard.jsonl:
`{"card":"cNN","cell":"(Δ,D)","idea":"<one line>","code":"<path>","command":"<exact command of the best run>",
"score":<vertices of your best VALID graph, or 0>,"valid":true|false|null,"sol":"<path of the solution file>",
"best_cost":<lowest cost if nothing solved>,"next":"<one line>"}`
Then reply to the director in at most 5 lines.
