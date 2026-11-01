# beyond-d14 squad, round 3 — shared header (read this first, then your card)

Job beyond-d14 (2026-11-01, Opus director). Goal: raise the D = 14 column of the bipartite degree-diameter table at
Δ = 3..8. All six cells already have checked values from job beyond-d13 earlier today (7 squad rounds); you are trying
to BEAT them. Values to beat (graph order = 2N for Haar graphs):

| cell | value to beat (after round 2) | how it was made | notes |
|---|---:|---|---|
| (3,14) | 7,004 | director: regular lift of a 2+2 cubic base (p = 2) over the Frobenius group Z103 x\|_8 Z17 (order 1,751), salift_s, 40 CPU-s | p = 3: 6,486 (Z47 x\| Z23, r2/d04); p = 4: 6,328; Foster census CSS(6272,7) 6,272 |
| (4,14) | 503,014 (N = 251,507) | r2/d07: Haar graph of Z5849 x\|_5711 Z43 (prime m), random S, hmeta screen + chain | r1/c05: Z3079 x\| Z81 498,798 |
| (5,14) | 13,105,798 (N = 6,552,899) | r1/c08: Haar graph of Z152393 x\|_149882 Z43, random S, hmeta (4 s) | near miss Z153511 x\| Z43 (N 6,600,973) cost 1 (r1/c08/s6_153511_43.txt.best) |
| (6,14) | 192,314,952 (N = 96,157,476), check running | r2/d13: PSL(2,107) x Z157, ORBIT="3 2 0" | r1/c12: SL(2,137) x Z37 190,269,984 VALID |
| (7,14) | 1,709,227,632 (N = 854,613,816), check running | r2/d15: PSL(2,167) x Z367, ORBIT="3 2 1", found by RANDORB=8 (cost 0 in about 1 of 8 random symmetric S) | also SL(2,241) x Z61 (853.8M); r1/c15 SL(2,233) x Z67 VALID |
| (8,14) | 11,325,238,056 | director only | |

Size law (research/frontier/SIZE_LAW.md): a random-like S misses about mu = N exp(-W/N) group elements, W = number of
cross-side words, W(d,14) = sum_{i<7} d (d-1)^(2i). Search reaches cost 0 up to some mu* (larger mu = larger N =
harder). Evaluations are CHEAP here: one cost evaluation takes ~1 ms at (4,14), ~10 ms at (5,14), ~0.1 s at (6,14),
~1 s at (7,14) (single thread, bit-parallel BFS). So thousands of evaluations per card are possible; use them.

## Round 2 (this job; the cards were stopped after ~19 minutes by a container restart) found / ruled out

- (3,14): smaller bases win. p = 2 (2+2 base) over Frobenius groups: orders 1,629-1,751 all solved in 40 CPU-s
  (7,004 = 4 x 1,751, Z103 x|_8 Z17); 1,778-1,884 stall: Z199 x| Z9 (1,791, 7,164) cost 6 (r2/d06/sols/L22_meta_199_9_43.sol.best),
  Z61 x| Z30 (1,830) cost 10 (director, research/frontier/beyond14/ownsmall/runs/d14_g1800s_7.sol.best, table g1800s.txt
  id 7), Z113 x| Z16 (1,808) cost 16, Z157 x| Z12 (1,884) cost 74, F19^2 x| Z5 (1,805) cost 20.
  p = 3: Z47 x| Z23 (1,081) solved (6,486); Z61 x| Z20 (1,220, 7,320) cost 24, Z97 x| Z12 (1,164, 6,984) cost 24.
  p = 4: 6,328 (Z113 x| Z7); 819-889 stall at 6-26. p = 1 (cubic Haar) via salift: cost 56-72 at ~7,164. p = 6 and
  products at p = 2 of order 2,181+: thousands. Tables: research/frontier/beyond14/ownsmall/mktab.py now also builds
  aff2:p:k = F_(p^2) x| Z_k (Frobenius, k | p^2 - 1).
- (4,14): d07's recipe (prime-m metacyclic, 20-s hmeta screens, chain the best) gave Z5849 x| Z43 (503,014); cost-2 states
  at Z6151 x| Z41 (N 252,191) and Z7211 x| Z35 (N 252,385, cost 3) in r2/d07/scr/. Order-2 orbit forms at Δ = 4 (r2/d09)
  and lifts of 2+2 4-regular bases over Z_m x| Z7 (r2/d08, tool r2/d08/lift4.c: cost 4 at 397K vertices; k = 7 is too
  small, use k >= 30) unresolved.
- (5,14): order-2 orbit forms in SL(2,q) x Z_n stall at 18-36 (r2/d11), in metacyclic groups far worse (r2/d12, cost 3,921).
- (6,14): PSL(2,107) x Z157 (96.16M) solved; (7,14): RANDORB=8 screens solve about 1 S in 8 at 853-855M, min cost 3 above 855M.

## Round 1 (this job) found / ruled out

- (3,14): cyclic lifts are capped below the census: Pappus n = 318/319 cost 2 (r1/c01); Tutte 8-cage n = 210 cost 30,
  Tutte 12-cage n = 50 cost 376, Foster graph n = 70 cost 270 (r1/c02); metacyclic voltages on the Pappus graph (18
  vertices) cost 6-8 at 5,724 (r1/c03); cubic Haar graphs H(G,{e,x,y}) of AGL(1,41) x Z2 etc. cost 6 at 6,560 (r1/c04).
  What works: SMALL bases (4+4) with a NON-ABELIAN voltage group of order ~800, base and voltages annealed together
  (the method of the lab's (3,10) 810, (3,11) 1,344 and (3,12) 2,368 records, job own-small).
- (4,14): prime-m metacyclic groups screened with hmeta (20 s each) at N 249K-251K: Z3079 x| Z81 solved in 9 s.
- (5,14): order-2 orbit form "2 2 1" in PSL(2,163) x Z3 solved (median random cost 41, min 10); SL(2,79) x Z13 random S
  stalls at cost 1.
- (6,14): "3 2 0" screen (40 random S, min/median cost): SL(2,137) x Z37 0-1/15, SL(2,239) x Z7 3/16, SL(2,79) x Z193
  4/49, PSL(2,89) x Z271 12/57. Orbit forms "6 1 0" (degenerate), "2 3 0" (cost 1,306), "3 1 3" are far worse (r1/c13).
- Machine notes: haar_big0 ignores SIGTERM during setup (use kill -9 on your OWN PID if it overruns); salift_s counts
  CPU seconds, so under load (load average 12-15 on 4 cores) a "30 s" run takes ~2 minutes of wall time: give it at most
  25 CPU seconds per command and chain from OUT.best.

## Already found / already ruled out (beyond-d13, do not repeat)

- (3,14): cyclic lifts of GP(10,3) (Z280, Z282 VALID; n = 283-285 cost >= 2), Pappus (Z317 VALID; Z315/316 cost 4/2),
  Tutte 8-cage (n = 187 cost 2), Heawood, Moebius-Kantor, F26A, GP(n,k) family, random cubic bases: all below. Haar
  graphs of groups of order ~2,520-2,860 with S = {e,x,y} exhaustive: best PSL(2,7) x Z15 = 5,040. Metacyclic groups
  with k <= 8: nothing. lift.c needs proper cooling (its cooling runs over L = 20,000 evaluations by default: pass
  T0 T1 L, e.g. 2 0.05 1200, for short runs); the 1-opt + tabu finisher scan (bin/scan_h02) closed cost-2 near misses.
- (4,14): orbit forms in SL/PSL (one free element) stall at mu 12-17; GQ(3,3) cyclic lifts (cost 612), K4,4 lifts
  (cap ~31k): useless. Metacyclic random S won: Z7001 x| Z35 490,070, Z4027 x| Z61 491,294, Z2731 x| Z91 497,042.
- (5,14): orbit form "3 1 2" stalls (cost 18); random S wins: PSL(2,227) 11.7M, PSL(2,53) x Z83 12.35M, SL(2,97) x Z7
  12,776,064 (haar_gen3), metacyclic Z148781 x| Z43 12,795,166 (hmeta). Four more metacyclic groups at cost 1.
- (6,14): ORBIT "3 2 0" in SL/PSL x Z_n won (SL(2,97) x Z103, PSL(2,137) x Z73); PSL(2,83) x Z331 stuck at 3,
  metacyclic random S at Δ = 6 roughly break-even with SL/PSL at D = 11 (r7/j14 RULE.md).
- (7,14): ORBIT "3 2 1": PSL(2,223) x Z151 (9 evaluations from a random start, mu 6.2), SL(2,269) x Z43 1,673,976,240;
  PSL(2,109) x Z1291 cost 30. Nobody pushed (7,14) beyond mu 6.2.
- General: odd-order (Frobenius) groups matter at ODD D only (D = 14 is even). At even D the binding words are the
  cross-side words S(S^-1 S)^6 (length 13), which are not inversion-closed, so no element class is special.

## Tools (prebuilt in research/frontier/beyond14/bin/; sources in research/frontier/beyond14/tools/ and research/frontier/)

- `hmeta d D seconds seed K outfile m k r` — metacyclic Z_m x|_r Z_k (r^k = 1 mod m), random S (e + d-1 free),
  bit-parallel. Env: THREADS, T0 (2), T1 (0.2), REHEAT (40), TARGP (70), START=sol, EVAL=sol, OPT1=1 (exhaustive 1-opt
  from START), OPT2=1 (exhaustive 2-opt from START; OPT2PAIR=i,j for one pair). Prints a RESULT line; writes outfile
  on cost 0 and outfile.best on every improvement. beyond-d13's good settings: T0=8 T1=1 REHEAT=400, K=16.
  Group lists: `python3 tools/enumeta.py Nlo Nhi [kmin]` (all metacyclic groups in an order range),
  `python3 tools/mpick.py d D Nlo Nhi` (Frobenius groups with size-law mu).
- `haar_big0 d D seconds seed K outfile sl|psl p n` — SL(2,p) x Z_n / PSL(2,p) x Z_n with alpha-orbit S.
  Env ORBIT="k m f" (orbits of size k, m orbits, f-1 fixed generators plus e if f >= 1; f = 0: free orbits, no e),
  THREADS, RANDORB=m (cost statistics of m random symmetric S, no search), EVAL=sol, START=sol (needs the orbit form;
  with f = 0 use the <out>.orb file), TMAX, TMIN, COOLSTEPS, REHEATSTEPS, TARGP. Header of tools/haar_big0.c explains all.
  Group picker: `python3 tools/pick.py d D mu_lo mu_hi [k] [maxn]` (SL/PSL x Z_n with size-law mu in a range).
- `haar_gen3 d D seconds seed K outfile GROUP... n` — generic random-S annealer, many families (meta, sl, psl, pgl,
  agl1, prod G1 G2, prime-power fields); header of research/frontier/haar_gen3.c. Slower per evaluation than hmeta.
- `lift BASE n D seconds seed OUTPREFIX [T0 T1 L]` (cubic), `liftd` (env DEG for other degrees), `scan_h02 BASE n D
  seconds seed OUTPREFIX [tenure]` (1-opt + tabu finisher; START=voltage file). Bases in research/frontier/beyond14/bases/
  (first line = number of vertices, then edges "u v", sides A = [0,h), B = [h,2h)). Incumbent (3,14) voltages:
  research/frontier/beyond14/incumbents/d3D14_pappus_n317.volt (base bases/pappus_j13.txt).
- Incumbent solutions: research/frontier/beyond14/sols/ (d4D14_meta_3079_81_1863_c05.txt, d5D14_psl_163_3_orb2-2-1_c11.txt,
  d6D14_sl_137_37_orb3-2-0_c12.txt, d7D14_psl_223_151_orb3-2-1_h14.txt, ...).
- Regular lifts of small cubic bases (research/frontier/beyond14/ownsmall/, from job own-small): `python3 mktab.py
  TABLE.txt meta:m:k:r [prod:meta:a:1:1/meta:m:k:r ...]` writes group multiplication tables (index 0 = identity;
  Z_m x|_r Z_k needs r^k = 1 mod m; Z_a = meta:a:1:1); `D=14 ./salift_s p TABLE.txt ID SEED CPUSECONDS [T0 T1] OUT.sol`
  anneals a p+p cubic base and its voltages together (cost = (root, vertex) pairs beyond distance 14; START=OUT.sol.best
  continues; OUT.sol written at cost 0); `D=14 ./polish p TABLE.txt ID START.best OUT.sol` is an exact steepest-descent
  finisher (single voltage changes, endpoint swaps, voltage pairs: slow for groups above ~300 elements);
  `python3 build_lift_tab.py SOL TABLE.txt EDGES` writes the lift's edge list, then `../bin/apsp EDGES 3 14`.
  The 6,328 solution: ownsmall/runs/d14_g800s_1.sol (table ownsmall/g800s.txt, id 1).
- Checkers (run on your best find before reporting it as valid):
  Haar graphs up to ~20M vertices: `python3 research/frontier/build_haar2.py SOL` (all families; exit code 0 = valid).
  Lifts / any edge list: `research/frontier/beyond14/bin/apsp EDGES d D` (e.g. `apsp g.edges 3 14`; first line n, then
  "u v" lines; it must print RESULT VALID). 
  SL/PSL above 20M vertices: do not check yourself; report the cost-0 solution file and the director runs
  research/frontier/beyond14/bin/haarcheck_gen on it.

## Machine rules (strict; 4 cores and 15 GB shared by 16 cards and the director)

- Every heavy command: `timeout 105 nice -n 10 env THREADS=1 <cmd>`. Keep each Bash command under 110 s. Longer
  searches = chains of short runs (START from the previous .best). Never use run_in_background, never `&`.
- At most ~1 GB memory per process. Work only in your card folder research/squads/beyond14/r3/<card>/ (create it);
  read anything. If you change a C tool, copy it into your folder and build there: gcc -O3 -march=native -fopenmp -o X X.c -lm
- No git commands that write. Never kill processes except your own by PID (no pkill/killall with patterns). Do not use
  the Agent tool, remote-session tools, or schedulers.
- Time box: about 35 minutes of wall time, and USE it: round-1 cards stopped after 6-13 minutes. After a find, keep
  pushing (next larger size) until the time box is over; chain runs. Then finish with the scoreboard line and the reply.

## Output

Append ONE JSON line to research/squads/beyond14/r3/scoreboard.jsonl:
{"card": "c07", "cell": "(5,14)", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>",
 "score": <vertices of your best VALID graph above or below the record, else 0>, "valid": true|false,
 "sol": "<path of the solution / voltage file / edge list>", "best_cost": <lowest cost reached at the largest size tried>,
 "near_miss": "<path, vertices, cost of your best cost<=3 file ABOVE the record, or empty>", "next": "<one line>"}
Then reply to the director in at most 5 lines (best result, whether it beats the record, the one thing to try next).
