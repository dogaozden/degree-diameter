# beyond-d11b squad, round 1: shared rules (read this first, then your card)

Job beyond-d11b (2026-11-01, Opus director, branch claude/beyond-d11-d12-new-cells-3t3djx). Problem: bipartite
degree-diameter: the largest Δ-regular bipartite graph of diameter D. Our values come from Haar graphs H(G,S):
vertices (g,A),(g,B), g in G, edges (g,A)~(s g,B), s in S, |S| = Δ, e in S; 2|G| vertices. Right multiplication by G
is transitive on each side, so BFS from (e,A) and from (e,B) gives the exact diameter. Odd D = 2h+1 needs BOTH
(S^-1 S)^h = G and (S S^-1)^h = G (two conditions); even D needs one.

The director is filling the new cells (15,11), (16,11), (14,12) and raising (12,12), (13,12) with ~30-billion-vertex
Haar graphs on this machine. **Your job: raise one of the smaller D = 11 or D = 12 cells with an idea that has NOT been
tried, or produce a clear negative or a usable rule.** A new group family, structure or construction that works is worth
more than a 0.5 % raise by an old method.

## Values to beat (vertices; all checked)
D = 11: (3,11) 1,474; (4,11) 24,360; (5,11) 297,648; (6,11) 2,094,960; (7,11) 11,012,976; (8,11) 45,329,808;
(9,11) 155,250,816; (10,11) 460,691,568; (11,11) 1,241,299,248.
D = 12: (3,12) 2,176; (4,12) 68,544; (5,12) 1,041,768; (6,12) 9,366,240; (7,12) 59,838,504; (8,12) 284,095,056;
(9,12) 1,105,785,120.
How they were made: (3,11) metacyclic Z67 x|_9 Z11 (odd order 737), (3,12) Z68 x|_3 Z16 (exhaustive pair search); all
others SL(2,p) x Z_n (odd D) or PSL(2,p) x Z_n (even D) with S closed under alpha = (conjugation by a matrix of order 3)
x (z -> r z, r of order 3 mod n), ORBIT "3 m f" (S = f alpha-fixed generators incl. e + m orbits of size 3; f = 0 means
m free orbits, no e). Size law (research/frontier/SIZE_LAW.md): a random S on a group of order N leaves about
mu = N exp(-W/N) elements uncovered (W = number of same-side words); the values above sit at mu ~ 8-15.

## Already found or ruled out (do NOT redo; from jobs new-cells-beyond and beyond-d11)
- Odd D: PSL(2,p) is bad (~p^2/2 involutions; words reaching an involution pair up, so it is missed with prob.
  ~exp(-lambda/2)); central elements are missed ~exp(-lambda/h) (rotation clumps); -I in SL is the worst single hole.
  Hence SL(2,p) x Z_n with small n. Details: research/frontier/beyond11/ODD_D_HOLES.md.
- Orbit orders k = 2, 4, 5, 6 at D = 11 (worse than k = 3); self-dual (transpose-closed) S; annealing knobs (K, TARGP,
  BOUNDCUR); moving fixed generators; -I as a generator; a generator x with x^2 = -I (weak); meet-in-the-middle
  near-miss finisher; composite n at (7,11); n/p >= 40 at odd D.
- Metacyclic groups by annealing at Δ = 4 (any k): 17,600 at (4,11), 48,000 at (4,12) (below the values).
  Metacyclic exhaustive cubic sweeps: all Z_m x|_r Z_k of order 541-1,100 at D = 11, 931-1,728 at D = 12.
- Near-miss plateaus (cost 1-3 for thousands of evaluations): (6,11) SL(2,103); (7,11) SL(2,67) x Z19; (9,11)
  SL(2,137) x Z31; (10,11) SL(2,617); (6,12) PSL(2,211); (9,12) PSL(2,167) x Z241. Do not resume these.

## Tools (absolute paths, already built; do not rebuild them, copy the source if you need a variant)
B = /home/user/degree-diameter/research/squads/beyond11b/bin
- `$B/haar_sym d D secs seed K OUT GROUP... n` : annealing Haar search, all families of haar_gen3 (meta m k r, sl q,
  psl q, pgl q with q a prime or prime power, agl1 q, prod G1 G2, cyc, heis q) x Z_n. Env ORBIT="k m f", RANDORB=m,
  THREADS=1, AFROB=j (alpha = field automorphism x -> x^(p^j) on GF(p^e)), ALPHA=<index>, AR=<r>. Source and full
  option list: /home/user/degree-diameter/research/structured/haar_sym.c (header comment). Writes OUT on cost 0.
- `$B/haar_gen3 ...` : same CLI without orbits (plain random S). Source research/frontier/haar_gen3.c.
- `/home/user/degree-diameter/research/frontier/beyond11/bin/haar_big0 d D secs seed K OUT sl|psl p n` : the big-group
  search (prime p only), env ORBIT, START, RANDORB, EVAL, UNCPRINT. Memory N/2 bytes. Source research/frontier/beyond11/haar_big0.c.
- `python3 /home/user/degree-diameter/research/frontier/beyond11/pick.py d D mu_lo mu_hi k maxn` : SL/PSL(2,p) x Z_n
  groups with their size-law mu.
- `$B/exh3 TABLE.bin D [OUTPREFIX]` : exhaustive cubic Haar search over a group table; tables from
  `python3 /home/user/degree-diameter/research/squads/beyond11b/tools/groups.py SPEC OUT.bin` (SPEC grammar in its
  header: cyc, meta, dih, semi p k a b c d = Z_p^2 x| Z_k, sl2/psl2/pgl2 p, agl1 p, heis p, perm, products "A x B").
  Sweep driver example: research/squads/beyond11b/tools/sweep_meta.py. Tables are N*N*2 bytes: N <= 5,000.
- Checkers (the scorer): `python3 /home/user/degree-diameter/research/frontier/build_haar2.py SOL.txt` for haar_sym /
  haar_gen3 / haar_big0 solution files (use only for 2N <= 2,000,000: it is numpy and memory-hungry);
  `OMP_NUM_THREADS=1 /home/user/degree-diameter/research/frontier/beyond11/bin/haarcheck_gen SOL.txt` (sl/psl q, prod;
  N <= 3e7); `$B/apsp EDGES d D` (all-pairs on an edge list "n" then "u v" lines; n <= 400,000) for any other graph.
  A card's "valid" is a claim; the director re-checks every find.

## Machine rules (4 cores and 15 GB shared by 16 cards and the director's 7-11 GB jobs)
- Every heavy command: `timeout 105 nice -n 10 <cmd>` with THREADS=1 and secs <= 100. **Never start a command that
  runs longer than 110 s** (a longer command goes to the background and you sit idle). Chain runs instead: restart
  from the saved best state with a new seed (haar_big0: START=OUT.best; f = 0: START=OUT.best.orb).
- One process at a time. **Memory cap: 180 MB per card** unless your card says otherwise (the director's checks need
  11 GB; going over can kill a 40-minute check). haar_big0 prints its own memory estimate on line 1 (about N/2 bytes);
  for other programs estimate before running (a byte per element per bitset, tables N/nH*d*4 bytes, etc.).
- The director's jobs run at nice 0 and yours at nice 10, so runs can be 2-5x slower than quoted. That is expected.
- No git commits. Work only in your folder /home/user/degree-diameter/research/squads/beyond11b/r1/<card>/.
- **Time box: about 25 minutes of wall time from your first command. Use all of it** (earlier rounds stopped after 5-10
  minutes; that wastes the slot). Then write the scoreboard line and stop.

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/beyond11b/r1/scoreboard.jsonl:
{"card": "gNN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,D)",
 "score": <vertex count of your largest diameter-<=D graph, or 0>, "beats": "<value it beats, or no>",
 "valid": "<checker and verdict, or none>", "file": "<solution or edge-list path, or none>",
 "finding": "<one line: what you learned, with numbers>", "next": "<one line>"}
Then reply to the director in at most 5 lines.
