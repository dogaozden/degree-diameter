# beyond-d11 squad, round 1: shared rules (read this first)

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

## Already found (do not redo)
- (11,11) 1,170,162,000: SL(2,251) x Z37, ORBIT "3 3 2", mu = 3.31, solved in 53 evals. VALID.
- (12,11) 2,874,207,072: SL(2,263) x Z79, ORBIT "3 4 0" (f = 0), mu = 3.43, solved in 5 evals.
- (11,12) 10,474,157,232: SL(2,307) x Z181, "3 3 2", mu 3.2, 5 evals. (12,12) 19,980,294,768: PSL(2,503) x Z157,
  "3 4 0", 1 eval. (13,12) 19,993,487,976: PSL(2,307) x Z691, "3 4 1", 1 eval. (D = 12 at Δ = 12, 13 are capped by the
  job's 20-billion-vertex limit, not by the search: nothing to push there.)
- Director is running (13,11) SL(2,229) x Z271 "3 4 1" (mu 3.15) and (14,11) SL(2,607) x Z31 "3 4 2" (mu 3.06).
## Already ruled out or known (do not repeat)
- f = 3 with k = 3 (three commuting letters e, t1, t2) loses 8-10 % of words to collisions; f = 0 is better whenever
  3 | Δ (research/structured/STRUCTURE.md section 8).
- Orbits of order 2 did much worse than order 3 at (9,11) and (5,11) (181 and 388 holes).
- A cyclic factor much larger than p hurts: SL(2,23) x Z433 stalled at (7,11) while SL(2,43) x Z67 solved.
- Non-Haar families (polygon covers, lifts of generalized polygons, route charts) are orders of magnitude smaller at D >= 8.
- Larger orbits k cost through fixed points: an alpha-fixed element (about p of them) is uncovered with probability about
  exp(-lambda/k), lambda = W/N ~ 19 at these cells (STRUCTURE.md section 1: mu_eff = mu/k + |Fix| exp(-lambda/k)).

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/beyond11/r1/scoreboard.jsonl:
{"card": "cNN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,D)",
 "score": <vertex count of your largest best=0 graph, or 0>, "best_cost_at_larger": "<group, mu, best cost reached>",
 "valid": "search cost 0 | haarcheck_gen VALID | none", "file": "<solution path or none>", "next": "<one line>"}
Then reply to the director in at most 5 lines.
