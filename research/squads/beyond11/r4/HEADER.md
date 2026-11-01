# beyond-d11 squad, round 4: shared rules (read this first)

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

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/beyond11/r4/scoreboard.jsonl:
{"card": "fNN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,D)",
 "score": <vertex count of your largest best=0 graph, or 0>, "best_cost_at_larger": "<group, mu, best cost reached>",
 "valid": "search cost 0 | haarcheck_gen VALID | none", "file": "<solution path or none>", "next": "<one line>"}
Then reply to the director in at most 5 lines.

## Rules learned in rounds 1-3 (use them)
- ODD D (research/frontier/beyond11/ODD_D_HOLES.md): words reaching an involution pair up, words reaching a central
  element come in rotation clumps, so these elements stay uncovered far more often than others. PSL(2,p) has ~p^2/2
  involutions, SL(2,p) only -I; G x Z_n has n (PSL) or 2n (SL) central elements. So at odd D use **SL(2,p) x Z_n with
  small n (1, 7, 13, 19, 31) and large p**. PSL at odd D and large n at odd D both failed in round 2.
- EVEN D: neither effect exists; the special elements are the alpha-fixed ones (about p in SL, p/2 in PSL, each missed
  with probability ~exp(-lambda/3)). Prediction (untested): prefer PSL and smaller p (larger n is fine).
- When 3 | Δ use f = 0 (ORBIT "3 m 0"); otherwise f = 1 or 2 ("3 m 1", "3 m 2"). k = 3 throughout.
- Calibration: mu ~7 solves within ~300 evals, mu ~10 within ~1,000 (P = 0.5). Runs starting above cost 30 at mu >= 8
  rarely solve: restart with a new seed instead.
- Checking: run haarcheck_gen yourself only when N <= 3e7 (else report the file; the director checks).
- Values to beat are in your card. Every find must beat the current value for its cell.
- Memory: haar_big0 prints its own estimate on its first line; that number is the real need (groups with n = 1 have
  padded rows and need more than N/2 bytes). Your cap is 0.6 GB unless the card says otherwise.
- Round 3 values now standing (beat these): (5,11) 297,648; (6,11) 2,083,536; (7,11) 11,012,976; (8,11) 45,329,808;
  (9,11) 155,250,816; (10,11) 460,691,568; (5,12) 1,041,768; (6,12) 9,366,240; (7,12) 59,838,504; (8,12) 279,900,096;
  (9,12) 1,105,785,120; (10,12) 3,699,605,280; (4,11) 19,152; (4,12) 50,160.
- Composite n (products of primes = 1 mod 3, e.g. 91 = 7 x 13, 133, 247) also work with k = 3 and fill gaps in the group
  list (card r3/e16); keep n <= ~600.
