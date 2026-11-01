# beyond-d14 squad, round 1 — shared header (read this first, then your card)

Job beyond-d14 (2026-11-01, Opus director). Goal: raise the D = 14 column of the bipartite degree-diameter table at
Δ = 3..8. All six cells already have checked values from job beyond-d13 earlier today (7 squad rounds); you are trying
to BEAT them. Values to beat (graph order = 2N for Haar graphs):

| cell | value to beat | how it was made | size-law mu |
|---|---:|---|---:|
| (3,14) | 6,272 (census) / 5,706 (lab) | Foster census CSS(6272,7), a semisymmetric graph (not ours; found 22:55 UTC by the director, apsp VALID); the lab's own best is the Z317 lift of the Pappus graph (18 vertices) | 16.9 / 9.2 |
| (4,14) | 497,042 (N = 248,521) | Haar graph of Z2731 x\|_2400 Z91, random S (hmeta) | 16.5 |
| (5,14) | 12,795,166 (N = 6,397,583) | Haar graph of Z148781 x\|_85175 Z43, random S (hmeta) | 5.4 |
| (6,14) | 187,990,656 (N = 93,995,328) | Haar graph SL(2,97) x Z103, S = 2 free alpha-orbits of size 3 (haar_big0 ORBIT="3 2 0") | 8.4 |
| (7,14) | 1,674,490,944 (N = 837,245,472) | Haar graph PSL(2,223) x Z151, S = {e} + 2 orbits (ORBIT="3 2 1") | 6.2 |
| (8,14) | 11,325,238,056 | PSL(2,397) x Z181 (director only; not for cards) | 12.1 |

Size law (research/frontier/SIZE_LAW.md): a random-like S misses about mu = N exp(-W/N) group elements, W = number of
cross-side words, W(d,14) = sum_{i<7} d (d-1)^(2i). Search reaches cost 0 up to some mu* (larger mu = larger N =
harder). Evaluations are CHEAP here: one cost evaluation takes ~1 ms at (4,14), ~10 ms at (5,14), ~0.1 s at (6,14),
~1 s at (7,14) (single thread, bit-parallel BFS). So thousands of evaluations per card are possible; use them.

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
- Incumbent solutions: research/frontier/beyond14/sols/ (d4D14_meta_2731_91_i04.txt, d5D14_meta_148781_43_i07.txt,
  d6D14_sl_97_103_orb3-2-0_g07.txt, d7D14_psl_223_151_orb3-2-1_h14.txt, ...).
- Checkers (run on your best find before reporting it as valid):
  Haar graphs up to ~20M vertices: `python3 research/frontier/build_haar2.py SOL` (all families; exit code 0 = valid).
  Lifts / any edge list: `research/frontier/beyond14/bin/apsp EDGES d D` (e.g. `apsp g.edges 3 14`; first line n, then
  "u v" lines; it must print RESULT VALID). (Corrected 22:56 UTC: the first version of this header omitted d D.)
  SL/PSL above 20M vertices: do not check yourself; report the cost-0 solution file and the director runs
  research/frontier/beyond14/bin/haarcheck_gen on it.

## Machine rules (strict; 4 cores and 15 GB shared by 16 cards and the director)

- Every heavy command: `timeout 105 nice -n 10 env THREADS=1 <cmd>`. Keep each Bash command under 110 s. Longer
  searches = chains of short runs (START from the previous .best). Never use run_in_background, never `&`.
- At most ~1 GB memory per process. Work only in your card folder research/squads/beyond14/r1/<card>/ (create it);
  read anything. If you change a C tool, copy it into your folder and build there: gcc -O3 -march=native -fopenmp -o X X.c -lm
- No git commands that write. Never kill processes except your own by PID (no pkill/killall with patterns). Do not use
  the Agent tool, remote-session tools, or schedulers.
- Time box: about 35 minutes of wall time. Then finish with the scoreboard line and the reply.

## Output

Append ONE JSON line to research/squads/beyond14/r1/scoreboard.jsonl:
{"card": "c07", "cell": "(5,14)", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>",
 "score": <vertices of your best VALID graph above or below the record, else 0>, "valid": true|false,
 "sol": "<path of the solution / voltage file / edge list>", "best_cost": <lowest cost reached at the largest size tried>,
 "near_miss": "<path, vertices, cost of your best cost<=3 file ABOVE the record, or empty>", "next": "<one line>"}
Then reply to the director in at most 5 lines (best result, whether it beats the record, the one thing to try next).
