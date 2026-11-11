# beyond-d11 squad, round 2: shared rules (read this first)

Job beyond-d11 (2026-11-01, Opus director). Problem: bipartite degree–diameter, largest Δ-regular bipartite graph of
diameter D. We build Haar graphs H(G,S): vertices (g,A),(g,B), g in G, edges (g,A)~(s g,B), s in S, |S| = Δ, for
G = SL(2,p) x Z_n or PSL(2,p) x Z_n. Vertex count = 2|G|. S is closed under an automorphism alpha of order k
(conjugation by a fixed matrix of projective order k, times z -> r z on Z_n): ORBIT="k m f" means S = (f generators
fixed by alpha, the first one e) + m orbits of size k, Δ = f + k m. f = 0: S = m free orbits, no identity (solutions are
written as S s_0^-1 so the file starts with e; the orbit form is in <out>.orb).

## Tools (absolute paths; do not rebuild)
- Search: `/home/user/degree-diameter/research/frontier/beyond11/bin/haar_big0 d D secs seed K OUT sl|psl p n`
  env ORBIT="k m f", THREADS=1, START=<file> (resume from a .best file; for f = 0 use <out>.best.orb).
  Prints `start cost=..`, progress lines, and `RESULT ... best=<cost> evals=..`. best=0 means a candidate of diameter
  <= D; it then writes OUT (and OUT.best on every improvement). Source + options: research/frontier/beyond11/haar_big0.c
  (header comment). Memory: N/2 bytes (N = group order).
- Group picker: `python3 /home/user/degree-diameter/research/frontier/beyond11/pick.py d D mu_lo mu_hi k maxn` lists
  SL/PSL(2,p) x Z_n with n = 1 or n prime = 1 mod k (and k | p+-1), with the size-law value mu = N exp(-W/N) (expected
  number of uncovered elements per side for a random S; larger mu = larger graph = harder).
- Independent checker: `/home/user/degree-diameter/research/frontier/beyond11/bin/haarcheck_gen SOL` (OMP_NUM_THREADS=1),
  prints VALID/INVALID. Use it only on groups with N <= 1e8 (it takes ~0.4 s per million elements on one thread).
  Real-scale finds (N > 1e8): do NOT check them yourself; the director checks them (report the file path).

## Machine rules (4 cores and 15 GB shared by 16 cards and the director's billion-vertex jobs)
- Every heavy command: `THREADS=1 timeout 105 nice -n 10 <cmd>` with secs <= 100. Never start a command that runs
  longer than 110 s (a longer command goes to the background and you sit idle). Chain runs instead: after a run, restart
  with START=OUT.best (f >= 1) or START=OUT.best.orb (f = 0) and a new seed, until your time box ends.
- One process at a time. Memory cap per card: as stated in your card. No git commits. Work only in your folder.
- Time box: about 25 minutes of wall time from your first command, then write the scoreboard line and stop.

- Time box: use the whole 25 minutes. Round-1 cards stopped after 5-10 minutes; that wastes the slot. Chain runs.
- Memory: haar_big0 reports its own estimate on its first line; the real peak is about N/2 bytes + 50 MB. Your cap is
  stated in your card and already allows for that.
- The director's jobs run at nice 0 and the cards at nice 10, so evaluations can be 2-5 times slower than the timings
  quoted. That is expected; keep chaining.

## Already found (do not redo)
- (11,11) 1,170,162,000 VALID: SL(2,251) x Z37, "3 3 2", mu 3.31.
- (12,11) 2,874,207,072 VALID: SL(2,263) x Z79, "3 4 0"; card r1/c04 found 2,976,066,240 (SL(2,239) x Z109, mu 7.0,
  being checked). The director is continuing SL(2,193) x Z211 (mu 10.3) from cost 2.
- (13,11) 6,508,747,920: SL(2,229) x Z271, "3 4 1", mu 3.15 (being checked). (14,11): director (SL(2,607) x Z31).
- (11,12) 10,474,157,232, (12,12) 19,980,294,768, (13,12) 19,993,487,976 (D = 12 checks pending; (12,12), (13,12) are
  at the job's 20-billion-vertex cap).

## Round 1 findings (what to build on, what not to repeat)
- The last holes of near misses are special elements: SL(2,193) x Z211 at (12,11) misses only -I (both sides);
  SL(2,443) x Z7 at (11,11) misses two alpha-fixed elements (the torus a I + b g of the order-3 matrix g).
- Director's explanation (to be tested): for odd D = 2h+1 the words reaching a CENTRAL element c are closed under cyclic
  rotation (s1^-1 s2 ... s_2h = c implies its rotation by two letters = c), so c is uncovered with probability about
  exp(-lambda/h) instead of exp(-lambda), lambda = W/N ~ 19, h = 5. G = SL(2,p) x Z_n has 2n central elements
  ((+-I, z)); PSL(2,p) x Z_n has n. Alpha-fixed elements (about p of them) are uncovered with probability about
  exp(-lambda/3). Prediction: at odd D prefer PSL with small n (7-31) and large p; at even D the shape matters less.
- k = 5 orbits: worse at (11,11) with p ~ 270 (c03: best cost 6 at mu 6); better at (11,9) with p = 41 (c10, one seed).
  k = 2 and self-dual S (transpose closure) are worse. K, TARGP, BOUNDCUR settings: no effect (c13).
- Bug fixed in haar_big0 (05:00 UTC): for k = 4, 6, 10 the old code chose alpha of the wrong order; k = 2, 3, 5, 7 were fine.
- RANDORB at (11,11), mu ~5.5 (c16): SL(2,359) x Z13 and SL(2,241) x Z43 lowest (median 21-22), n > p worse (40-44),
  PSL(2,1063) with n = 1 much worse (median 151, unexplained).
- Calibration (c15): mu ~7 solves within ~300 evals, mu ~10 within ~1,000 (P = 0.5); runs starting above cost 30 at mu >= 8
  rarely solve.

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/beyond11/r2/scoreboard.jsonl:
{"card": "dNN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,D)",
 "score": <vertex count of your largest best=0 graph, or 0>, "best_cost_at_larger": "<group, mu, best cost reached>",
 "valid": "search cost 0 | haarcheck_gen VALID | none", "file": "<solution path or none>", "next": "<one line>"}
Then reply to the director in at most 5 lines.
