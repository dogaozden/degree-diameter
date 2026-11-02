# raise-d9 squad, round 1: shared rules (read this first, then your card)

Job raise-d9 (2026-11-01/02, Opus director, branch claude/raise-d9-orbit-metacyclic-ndvfty). Problem: bipartite
degree-diameter: the largest Δ-regular bipartite graph of diameter D. **This job: raise our D = 9 values.**
Our values come from Haar graphs H(G,S): vertices (g,A),(g,B), g in G, edges (g,A)~(s g,B), s in S, |S| = Δ, e in S;
2|G| vertices. Right multiplication by G is transitive on each side, so BFS from (e,A) and from (e,B) gives the exact
diameter. D = 9 = 2h+1 (h = 4) is odd: it needs BOTH (S^-1 S)^4 = G and (S S^-1)^4 = G.

The director is pushing (17..20, 9) with haar_big0 on this machine (2 jobs x 2 threads). **Your job: raise one D = 9
cell with the idea on your card, or produce a clear negative or a usable rule.** A new group family, structure or
construction that works is worth more than a 0.5 % raise by an old method.

## D = 9 values to beat (vertices; all checked) and size-law mu at the current value
mu = N exp(-W/N), N = |G| = half the vertices, W = W(Δ,9) = 1 + sum_{i=1..4} Δ(Δ-1)^(2i-1) (same-side words per side).
A random S on a group of order N leaves about mu elements uncovered; plain annealing stalls near mu 8-15, orbit search
(S closed under an automorphism) got these D = 9 values to mu 23-47.

| Δ | value | group of the current value | mu | W(Δ,9) |
|---|---:|---|---:|---:|
| 3 | 506 (2013 table, never beaten) | voltage graph (Loz et al.) | 33.6 | 511 |
| 4 | 4,970 (2013 table, never beaten) | voltage graph (Loz et al.) | 47.4 | 9,841 |
| 5 | 29,756 | Z346 x|_29 Z43 = Z2 x (Z173 x| Z43), plain S | 41.9 | 87,381 |
| 6 | 127,296 | SL(2,17) x Z13, ORBIT "3 2 0" (2 free orbits) | 29.6 | 488,281 |
| 7 | 462,840 | PSL(2,29) x Z19, orbit k=3 | 38.2 | 2,015,539 |
| 8 | 1,341,600 | SL(2,25) x Z43 (field GF(25)), orbit k=3 | 29.7 | 6,725,601 |
| 9 | 3,499,776 | PSL(2,7) x SL(2,7) x Z31, ORBIT f=0 | 30.5 | 19,173,961 |
| 10 | 8,418,120 | PSL(2,59) x Z41, ORBIT "5 2 0" (orbits of size 5) | 42.4 | 48,427,561 |
| 11 | 17,323,152 | SL(2,43) x Z109, orbit k=3 | 23.3 | 111,111,111 |
| 12 | 35,445,648 | SL(2,83) x Z31, ORBIT "3 4 0" | 29.5 | 235,794,769 |
| 13 | 67,742,688 | SL(2,103) x Z31, orbit k=3 | 32.8 | 469,070,941 |
| 14 | 120,043,728 | SL(2,107) x Z49 (n composite!), orbit k=3 | 24.2 | 883,708,281 |
| 15 | 208,483,200 | SL(2,5) x SL(2,19) x Z127, ORBIT f=0 | 24.9 | 1,589,311,291 |
| 16 | 348,207,600 | SL(2,101) x Z169, orbit k=3 | 24.6 | 2,745,954,241 |
| 17-20 | 501.7M / 790.6M / 1,218.4M / 1,823.2M | director only | 2.6-2.9 | |

Solution files of these values: /home/user/degree-diameter/research/frontier/sols/d<Δ>D9_*.txt (format: header
"d D <group> n NCYC N NTOT", then d generator lines, first = e).

## Already found or ruled out (do NOT redo)
- Odd D theory (research/frontier/beyond11/ODD_D_HOLES.md, read the table there): involutions are missed with prob.
  ~exp(-lambda/2), central elements ~exp(-lambda/h) (h = 4 here), alpha-fixed (torus) elements ~exp(-lambda/3), where
  lambda = W/N. So PSL(2,p) (p^2/2 involutions) and SL(2,p) x Z_n with large n (2n central elements) pay extra holes.
  At D = 11 this made **SL(2,p) x Z_n with small n (1-19) and large p** the winning shape; at D = 9 nobody has tested
  that shape against the current values (most of them have n = 31-169).
- Odd-order centre-free **Frobenius groups Z_p x|_r Z_k** (p prime, k odd 13-63, r of order k mod p) beat SL/PSL at
  small N at D = 11/12 (research/frontier/beyond11/FROBENIUS.md: (4,11) at mu 44, (5,11) mu 20). k = 3 collapses, k = 7
  is bad. Orbit search on Frobenius groups degenerates (do not use ORBIT on meta groups).
- (5,9): 2,398 metacyclic and SL/PSL groups of order 14,280-15,186 were screened and annealed (2 sessions; Z761 x| Z19
  Frobenius included); above N = 14,878 the best groups stall at cost 2. Do not redo plain metacyclic annealing there.
- (4,9): Haar sweep N = 2,486-2,580 (1,538 groups, any metacyclic, 300 s) ended at cost 10-18; regular voltage lifts
  of orders 4,972-4,988 negative. (3,9): haar_gen3 sweep N = 254-275 best cost 30; 133 lift searches of orders 508-540
  best cost 18; field-affine 2+2 lifts exhaustively negative.
- Orbit orders k = 2, 4, 5, 6 were worse than k = 3 at D = 11 (but (10,9)'s value uses k = 5).
- Self-dual S, -I as a generator, annealing knobs (K, TARGP, BOUNDCUR), moving fixed generators: no gain at D = 11.
- Near the limit, solves come from MANY fresh seeds (1 in 5-15 runs), not from long runs; cost-1/2 states are usually
  true local minima.

## Tools (absolute paths, already built; do not rebuild them, copy the source if you need a variant)
B = /home/user/degree-diameter/research/squads/raise9/bin
- `$B/haar_big0 d D secs seed K OUT sl|psl p n` : big-group orbit search (G = SL(2,p) or PSL(2,p) x Z_n, p prime >= 5,
  gcd(p,n) = 1). Env ORBIT="k m f" (S = {e} + (f-1) alpha-fixed + m orbits of size k, d = f + k m; f = 0: m free
  orbits without e), THREADS=1, START=<OUT.best or OUT.best.orb for f = 0> (resume), RANDORB=m (cost statistics of
  m random symmetric S, no search), EVAL=<sol file>, UNCPRINT=1. Memory about N/2 bytes. Writes OUT on cost 0 and
  OUT.best at every improvement. Source and full option list: research/frontier/beyond11/haar_big0.c (header).
  Speed: ~0.4 s per evaluation at N = 2.7e8 with 1 thread; N = 1e7 ~0.02 s.
- `python3 /home/user/degree-diameter/research/frontier/beyond11/pick.py d D mu_lo mu_hi k maxn` : SL/PSL(2,p) x Z_n
  groups (n = 1 or a prime = 1 mod k) with their size-law mu, sorted by N. Example: `pick.py 11 9 23 30 3 200`.
- `$B/haar_sym d D secs seed K OUT GROUP... n` : annealing Haar search for all families (meta m k r, sl q, psl q, pgl q
  with q a prime power (field poly automatic), agl1 q, prod G1 G2, heis q, cyc) x Z_n; env ORBIT="k m f", RANDORB=m,
  THREADS=1, AFROB=j, ALPHA, AR. Source: research/structured/haar_sym.c (header has every option).
- `$B/haar_gen3 ...` (plain random S, same CLI as haar_sym without ORBIT; source research/frontier/haar_gen3.c),
  `$B/haar_gen3s` (+ SAVEBEST=<file>, START=<file>: save/resume), `$B/haar_gen3t` (+ TFULL=1 TARGP=100: targeted
  finisher). For Z_p x| Z_k keep k <= 63 (fast coset layout). Sources: research/squads/beyond11b/tools/.
- `$B/exh3 TABLE.bin D [OUTPREFIX]` : exhaustive cubic Haar search over a group table; tables from
  `python3 /home/user/degree-diameter/research/squads/beyond11b/tools/groups.py SPEC OUT.bin` (grammar in its header).
- Checkers (the scorer): `python3 /home/user/degree-diameter/research/frontier/build_haar2.py SOL.txt` (any haar_*
  solution file; only for 2N <= 2,000,000), `OMP_NUM_THREADS=1 $B/haarcheck_gen SOL.txt` (sl/psl q, prod; any N up to
  ~3e7 on a card), `$B/apsp EDGES d D` (all-pairs on an edge list "n" then "u v" lines; n <= 400,000) for any other
  graph. A card's "valid" is a claim; the director re-checks every find.

## Machine rules (4 cores and 15 GB shared by 16 cards and the director)
- Every heavy command: `timeout 105 nice -n 10 <cmd>` with THREADS=1 and secs <= 100. **Never start a command that
  runs longer than 110 s** (a longer command goes to the background and you sit idle). Chain runs instead: restart
  from the saved best state with a new seed (haar_big0: START=OUT.best; f = 0: START=OUT.best.orb; haar_gen3s: START=).
- One process at a time. **Memory cap: 300 MB per card** unless your card says otherwise.
- The director's jobs run at nice 0 and yours at nice 10, so runs can be 2-4x slower than quoted. That is expected.
- No git commits. Use only the shell and file tools: **never call session, messaging, agent or GitHub tools**
  (create_session, send_message, Agent, mcp__*). Append to the scoreboard with `>>` as ONE line of JSON (no line
  breaks inside); never rewrite the file.
- Work only in your folder /home/user/degree-diameter/research/squads/raise9/r1/<card>/ (create it).
- **Time box: about 25 minutes of wall time from your first command. Use all of it** (earlier rounds stopped after
  5-10 minutes; that wastes the slot). Then write the scoreboard line and stop.
- Save every valid solution file you find in your folder, with the cell in its name (d<Δ>D9_...).

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/raise9/r1/scoreboard.jsonl:
{"card": "<id>", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,9)",
 "score": <vertex count of your largest diameter-<=9 graph, or 0>, "beats": "<value it beats, or no>",
 "valid": "<checker and verdict, or none>", "file": "<solution or edge-list path, or none>",
 "finding": "<one line: what you learned, with numbers (best cost per group, mu)>", "next": "<one line>"}
Then reply to the director in at most 5 lines.
