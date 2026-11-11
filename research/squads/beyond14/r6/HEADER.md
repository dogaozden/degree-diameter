# beyond-d14 squad, round 6 (last) — shared header (read this first, then your card)

Job beyond-d14 (2026-11-01, Opus director). Goal: raise the D = 14 column of the bipartite degree-diameter table at
Δ = 3..8. All six cells already have checked values from job beyond-d13 earlier today (7 squad rounds); you are trying
to BEAT them. Values to beat (graph order = 2N for Haar graphs):

| cell | value to beat (after round 5) | how it was made |
|---|---:|---|
| (3,14) | 7,004 | 2+2 base over Z103 x\|_8 Z17 (salift_s) |
| (4,14) | 504,382 (N = 252,191) | Z6151 x\|_5694 Z41 (1-opt finisher) |
| (5,14) | 13,467,134 (N = 6,733,567) | Z100501 x\|_52125 Z67: cost-1 state, FIN, then a LOW-TEMPERATURE hmeta anneal (`T0=0.5 T1=0.1 TARGP=90 REHEAT=60`, K = 4) closed it (r5/g02) |
| (6,14) | 193,539,888 (N = 96,769,944) | SL(2,107) x Z79, best of 60 random symmetric S then a short anneal (r5/g09) |
| (7,14) | 1,732,018,320 (N = 866,009,160) | SL(2,179) x Z151, low-T anneal from cost 3 (r4/f15); PSL(2,1201) (866,161,200) check running |
| (3,12) side | 2,436 | 2+2 base over Z87 x\|_7 Z7 (r5/g14); lab had 2,368 |
| (3,13) side | 4,324 | 2+2 base over Z47 x\|_2 Z23 (director); beyond-d13 had 3,400 |
| (3,11) side | 1,344 (lab) | (r5/g14: 2+2 over a Z38 x\| Z9-type group, 1,368, cost 2, runs/B_2.sol.best) |

The finishing recipe that worked in round 5 (r5/g02): FIN (hole-directed) to move a cost-1 state sideways, then a
low-temperature hmeta anneal from the FIN output. Near misses left by round 5: (7,14) SL(2,359) x Z19 (N 879,090,480,
cost 1, a random S: research/squads/beyond14/r5/g12/r_sl359_19.sol.low); (6,14) SL(2,71) x Z271 (N 96,974,640, cost 3,
r5/g09/a_sl71_271_s27.sol.best); (3,13) Z55 x|_2 Z20 at p = 2 (4,400, cost 2, r5/g08/st1100.best); (3,11) 1,368 cost 2.

New shared tool (r4/f09): `research/frontier/beyond14/bin/hmeta_fin` = hmeta plus env FIN=1: from START, each round picks
a random slot, builds K candidates that force a word of length D-1 through that slot onto the uncovered element, and
keeps the best (sideways moves allowed); it rewrites OUTFILE every round (so OUTFILE is cost 0 only when the RESULT line
says "FIN cost0"). Usage: `FIN=1 START=state.sol timeout 105 nice -n 10 env THREADS=1
research/frontier/beyond14/bin/hmeta_fin d 14 95 SEED 200 OUT m k r`. It closed Z83267 x| Z79 (cost 1 -> 0) and Z73693 x| Z89.

Size law (research/frontier/SIZE_LAW.md): a random-like S misses about mu = N exp(-W/N) group elements, W = number of
cross-side words, W(d,14) = sum_{i<7} d (d-1)^(2i). Search reaches cost 0 up to some mu* (larger mu = larger N =
harder). Evaluations are CHEAP here: one cost evaluation takes ~1 ms at (4,14), ~10 ms at (5,14), ~0.1 s at (6,14),
~1 s at (7,14) (single thread, bit-parallel BFS). So thousands of evaluations per card are possible; use them.

## Round 5 (this job) found / ruled out

- (5,14): Z100501 x| Z67 closed (FIN + low-T anneal). Cost-1 states BELOW the new record no longer matter; above it
  (6.74-6.79M, r5/g15) costs were 4-5.
- (6,14): SL(2,107) x Z79 solved; SL(2,71) x Z271 at 3. (7,14): SL(2,359) x Z19 cost 1 (g12), SL(2,499) x Z7 cost 3 (g13).
- (3,14): cost-2 lift states resist every finisher (exact 1-opt, hole-directed 2-opt, r5/g06); p = 3, 4 with large-k
  groups reach cost 8 at 7,224-7,308 (g07). (3,12): Z87 x| Z7 solved at p = 2 (g14).

## Round 4 (this job) found / ruled out

- (3,14): nothing above 7,004. The p = 2 cost-2 states (Z37 x|_8 Z48, Z17 x|_2 Z104) are strict local minima for single
  moves (exact polish, r4/f01); F13^2 x| Z7 at p = 3 stays at 4 (f04); 16 more large-k groups at 1,752-1,764 are far
  (cost 162+, f02). Theory (r4/f05/LIFTS.md): at matched size the group's action order k changes start costs far more
  than the base size p; small-k groups collapse walk endpoints.
- (4,14): composite m works too (Z2 x (Z1877 x| Z67), 503,036, r4/f07) but nothing above 504,382; cost 1 at Z7211 x| Z35
  (f08, runs/m7211_k35_s2.sol.best) and Z6151 x| Z41 neighbours.
- (5,14): hole-directed finisher (f09) works; cost 1 remains at Z100501 x| Z67 (6.73M, r3/e10/c5_100501_67.sol.best),
  Z91397 x| Z73 (6.67M, r4/f10/s1_91397_73.sol.best), Z65651 x| Z101 (6.63M, r4/f10/s1_65651_101.sol.best), Z153511 x| Z43
  (6.60M, r4/f09/fin_153511.sol).
- (6,14): z-filter useless at Δ = 6 (f12); SL(2,241) x Z7 (97.98M) stuck at 4 (f13); cost 6 at SL(2,71) x Z271 (96.97M).
- (7,14): cost 3 at PSL(2,223) x Z157 (870.5M, r4/f15/rs_psl223_157.sol.low), PSL(2,167) x Z373 (868.6M), PSL(2,239) x Z127
  (866.9M, r4/f14/p239e.best).

## Round 3 (this job) found / ruled out

- (3,14): no new value. p = 2 has a hard floor at cost 6 just above order 1,751 for Frobenius groups (r3/e01, e16 with
  the base shape fixed); the best states above 7,004 are non-faithful metacyclic groups with LARGE k (Z37 x|_8 Z48,
  Z17 x|_2 Z104, cost 2) and PSL(2,7) x Z11 (cost 4). Only ~12 of ~400 groups of order 1,752-1,800 were tried (e02).
- (4,14), (5,14): many cost-1 and cost-2 states, no cost 0 (prime-m metacyclic, r3/e05, e08, e09, e10). Lifts of small
  bases do NOT help at Δ = 4, 5 (r3/e07: cost 26 at 503K; r3/e11: cost 0 only up to 8M at Δ = 5).
- (6,14), (7,14): random symmetric S keep solving just above the record (r3/e12, e15). r3/e14's trick: a cheap
  "z-uniformity" filter on random S (the Z_n components of the words spread evenly) before the costly evaluation.

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
- At most ~1 GB memory per process. Work only in your card folder research/squads/beyond14/r6/<card>/ (create it);
  read anything. If you change a C tool, copy it into your folder and build there: gcc -O3 -march=native -fopenmp -o X X.c -lm
- NEVER call any mcp__claude-code-remote__* tool (create_session, archive_session, send_message, triggers, ...) or the
  Agent / SendMessage tools, for any reason: three earlier cards did, against these rules.
- No git commands that write. Never kill processes except your own by PID (no pkill/killall with patterns). Do not use
  the Agent tool, remote-session tools, or schedulers.
- Time box: about 35 minutes of wall time, and USE it: round-1 cards stopped after 6-13 minutes. After a find, keep
  pushing (next larger size) until the time box is over; chain runs. Then finish with the scoreboard line and the reply.

## Output

Append ONE JSON line to research/squads/beyond14/r6/scoreboard.jsonl:
{"card": "c07", "cell": "(5,14)", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>",
 "score": <vertices of your best VALID graph above or below the record, else 0>, "valid": true|false,
 "sol": "<path of the solution / voltage file / edge list>", "best_cost": <lowest cost reached at the largest size tried>,
 "near_miss": "<path, vertices, cost of your best cost<=3 file ABOVE the record, or empty>", "next": "<one line>"}
Then reply to the director in at most 5 lines (best result, whether it beats the record, the one thing to try next).
