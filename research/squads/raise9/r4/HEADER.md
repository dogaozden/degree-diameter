# raise-d9 squad, round 4: shared rules (read this first, then your card)

Job raise-d9 (2026-11-01/02, Opus director, branch claude/raise-d9-orbit-metacyclic-ndvfty). Problem: bipartite
degree-diameter: the largest Δ-regular bipartite graph of diameter D. **This job: raise our D = 9 values.**
Our values come from Haar graphs H(G,S): vertices (g,A),(g,B), g in G, edges (g,A)~(s g,B), s in S, |S| = Δ, e in S;
2|G| vertices. Right multiplication by G is transitive on each side, so BFS from (e,A) and from (e,B) gives the exact
diameter. D = 9 = 2h+1 (h = 4) is odd: it needs BOTH (S^-1 S)^4 = G and (S S^-1)^4 = G.

The director is pushing (17..20, 9) with haar_big0 on this machine (2 jobs x 2 threads at nice 3, plus 2-thread checks). **Your job: raise one D = 9
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
| 17-20 | 543,962,400 / 850,056,960 / 1,328,920,800 / 1,998,558,432 (director: (17) SL(2,151) x Z79 "3 5 2" mu 13.2; (18) SL(2,191) x Z61 "3 5 3" mu 11.35; (19) SL(2,151) x Z193 "3 6 1" mu 15.7; (20) SL(2,233) x Z79 "3 6 2" mu 16.2) | director + round 4 | 11-16 | |

Solution files of these values: /home/user/degree-diameter/research/frontier/sols/d<Δ>D9_*.txt (format: header
"d D <group> n NCYC N NTOT", then d generator lines, first = e).

## Round 3 of this job (r3/scoreboard.jsonl) and what the director learned from it
- **The big-cell plateaus are TORUS holes.** At (17,9) SL(2,277) x Z13 "3 5 2" (mu 17.4) the last 2 uncovered elements are an
  inverse pair a I + b g with z = 0 (alpha-fixed, in the torus of the order-3 matrix g; about p such elements, each missed with
  probability ~exp(-lambda/3)). Central holes (+-I, z) are RARER than ODD_D_HOLES.md's model (w07: none in 6 sides where ~9 were
  predicted). So: **small p (50-150) and large n with gcd(r - 1, n) = 1 (only z = 0 alpha-fixed)**. With that shape the director
  solved (20,9) SL(2,233) x Z79 at mu 16.2 in 57 evaluations and (19,9) SL(2,151) x Z193 at mu 15.7 in 17 evaluations, where
  SL(2,457) x Z7, SL(2,313) x Z9, SL(2,523) x Z7 (large p, small n) stalled at cost 6-30.
- ORBIT split at odd D (w07, s18, s19): fewest fixed generators wins in random statistics: (18,9) "3 6 0" (median 24-31) <
  "3 5 3" (36-42) < "3 4 6" (84-132); (19,9) "3 6 1" < "3 5 4" < "3 4 7"; (17,9) "3 5 2" < "3 4 5". -I is a hole on both sides for
  f = 0 and f = 3. (But at (18,9) the director's only "3 6 0" run, SL(2,227) x Z37 at mu 15.8, stalled at 6, and "3 5 3" solved
  mu 11.35 in 81 evaluations.)
- (6,9) Frobenius farms: Z1559 x| Z41 cost 2 on 2 of ~60 fresh seeds (director and r2/f02), cost 4 often; Z2551 x| Z25 cost 2 once
  (g3); K = 16 >= K = 8 > K = 4 (g2). No solve yet.
- w09: a regular cover of a solved D = 9 Haar graph never has diameter 9 (a vertex of the base is reached by a unique
  non-backtracking walk of length <= 8). Do not try covers.

## Round 2 of this job (r2/scoreboard.jsonl): 17 cards, no raise
- (6,9) odd Frobenius: floor cost 6-8 over ~40 seeds (Z2551 x| Z25 6, Z1559 x| Z41 6-8, Z2377 x|_7 Z27 8, f01/f02/f03/w06);
  hole anatomy (f04): holes are inverse pairs, cost-6 states have ecc 10 on one side; 15k sampled single swaps: none < 6.
  Products with a Frobenius factor are worse (f08). (7,9) Z5659 x|_260 Z41 cost 16 (f05); (8,9) Frobenius k = 37/51 cost 18-26
  (f06); (9,9) Z35771 x|_921 Z49 cost 24 (f07). Small k (3-9) is hopeless everywhere.
- Near-miss farms did not move: (8,9) PSL(2,47) x Z13 stuck at 12 (n02), (11,9) PSL(2,97) x Z19 at 12 (n04), (12,9) SL(2,137) x Z7
  at 12 (n03). k = 5: (12,9) PSL(2,71) x Z101 "5 2 2" cost 16, no edge over k = 3 in random medians (k04); (11,9) k = 5 groups
  start at mu 30+ (k02). Single-orbit S ("5 1 f", exhaustive) far worse than plain S (k03). (16,9) SL(2,293) x Z7 has the
  same random median/mu ratio as the current group but stalled at 36 in 3 short runs (w05).
- Director, since round 2: (18,9) SL(2,191) x Z61 "3 5 3" solved at mu 11.35 in 81 evaluations ("3 6 0" on SL(2,227) x Z37 at
  mu 15.8 stalled at cost 6); (17,9) SL(2,277) x Z13 at mu 17.4 stuck at cost 2 (1,787 evals); (19,9) SL(2,263) x Z37 at mu 19.9
  cost 6; (15,9) PSL(2,151) x Z61 "5 3 0": resume stayed at 4, a fresh seed reached 14. Load average is ~20: expect 3-10x
  slower runs than quoted.
- Process: 5 more stray session-tool calls in round 2 (all rejected). **Never call any mcp__ tool or session tool.**

## Round 1 of this job (r1/scoreboard.jsonl; read the lines of the cards you build on)
All 16 cards: no raise. What we learned (use it):
- **(6,9) odd Frobenius groups are the lead (a03):** in random-S statistics Z2551 x|_7 Z25 (N 63,775, mu 30) has min 16 /
  median 72 against min 26 / median 140 for the current group SL(2,17) x Z13 (2000 samples each); Z1559 x|_84 Z41 min 14,
  Z4967 x|_307 Z13 min 16; k = 9 much worse. Plain annealing (haar_gen3s, 90 s) stalled at cost 6 on both Z2551 x| Z25 and
  Z1559 x| Z41 (3 seeds each), Z4967 x| Z13 at 12. Best states: r1/a03/best_*.txt.
- **(15,9) orbits of size 5 (m02):** PSL(2,151) x Z61 (N 105,005,400, just above the bar, mu 28.1), ORBIT "5 3 0", cost 4
  after ~400 evaluations; k = 5 random medians 77 vs 85 for k = 3 on the same group. The director now runs this state.
- (12,9) b02: SL(2,137) x Z7 (N 17,998,512, mu 36.8, ORBIT "3 4 0") cost 12 in 6 chained runs, while the current group
  SL(2,83) x Z31 reached only 30 in the same time; but at (13,9) small n was worse (b03). Shape is cell-dependent.
- (8,9) b06: PSL(2,47) x Z13 (N 674,544, mu 31.5), ORBIT "3 2 2", best cost 12 (random median 143 vs 236 for the current
  SL(2,25) x Z43). (14,9) b04: SL(2,167) x Z13 (mu 27.7) cost 12 in 6 x 95 s. (13,9) b03: small n is WORSE at D = 9
  (SL(2,257) x Z2 cost 40 vs the current group's 20); n = 17-31 with p ~ 100-130 is the shape there.
- m01 (17,9) shape table (r1/m01/SHAPES.md): SL(2,p) x Z_n, n in {1, 9, 13} or prime n with small gcd(r-1, n); PSL bad
  for p > 300 (involution holes); f = 5 worse than f = 2.
- Negatives: (3,9) exhaustive cubic Haar over all groups of order 254-330 (a02: none; min cost 8 at N = 272; cost 0 only
  at N = 253 = the table value); (4,9) Z17^2 x| Z9 cost 28, Z29^2 x| Z3 disconnected or 3,000+ (a01), lifts of a 2+2 base
  over Z251 x| Z5 cost 24, cyclic voltage groups collapse (w04); field-automorphism orbits (AFROB) on SL(2,27), SL(2,8)
  at (8,9)/(9,9) cost 20-22 (w02); products at (12,9) worse than SL(2,83) x Z31 (w01: random median 102-180 vs 86);
  twisted product Z173 x| PGL(2,29) 8x worse than the direct product (w03); (6,9)/(7,9) SL/PSL(2,q) shapes over GF(8),
  GF(16), GF(9), composite n: cost 21-95 (b07).
- Process: three round-1 cards called session tools (archive_session / send_message) with empty arguments; all failed.
  **Never call any mcp__ tool, Agent, SendMessage or session tool.**

## Already found or ruled out before this job (do NOT redo)
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
- haar_big0 uses about TWICE the memory it prints on line 1 (N/2 bytes printed). Round 4 caps: (17,9) 600 MB, (18,9) 900 MB, (6,9) 100 MB.
- Kill a stuck run with `timeout -s KILL`; plain timeout (TERM) does not stop haar_big0 at once.
- Every heavy command: `timeout 105 nice -n 10 <cmd>` with THREADS=1 and secs <= 100. **Never start a command that
  runs longer than 110 s** (a longer command goes to the background and you sit idle). Chain runs instead: restart
  from the saved best state with a new seed (haar_big0: START=OUT.best; f = 0: START=OUT.best.orb; haar_gen3s: START=).
- One process at a time. **Memory cap: 300 MB per card** unless your card says otherwise.
- The director's jobs run at nice 0 and yours at nice 10, so runs can be 2-4x slower than quoted. That is expected.
- No git commits. Use only the shell and file tools: **never call session, messaging, agent or GitHub tools**
  (create_session, send_message, Agent, mcp__*). Append to the scoreboard with `>>` as ONE line of JSON (no line
  breaks inside); never rewrite the file.
- Work only in your folder /home/user/degree-diameter/research/squads/raise9/r4/<card>/ (create it).
- **Time box: about 25 minutes of wall time from your first command. Use all of it** (earlier rounds stopped after
  5-10 minutes; that wastes the slot). Then write the scoreboard line and stop.
- Save every valid solution file you find in your folder, with the cell in its name (d<Δ>D9_...).

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/raise9/r4/scoreboard.jsonl:
{"card": "<id>", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,9)",
 "score": <vertex count of your largest diameter-<=9 graph, or 0>, "beats": "<value it beats, or no>",
 "valid": "<checker and verdict, or none>", "file": "<solution or edge-list path, or none>",
 "finding": "<one line: what you learned, with numbers (best cost per group, mu)>", "next": "<one line>"}
Then reply to the director in at most 5 lines.
