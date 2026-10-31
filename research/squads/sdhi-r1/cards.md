# Squad round sdhi-r1 (job selfdual-hi, Oct 31 2026)

Common part of every card (read it first).

**Background.** A Haar graph H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S, |S| = K. It is *self-dual* if
S is a union of orbits of psi(x) = u0 beta(x)^-1 (beta an automorphism of G, u0 in G); then the graph has a
side-swapping automorphism. The tool `research/selfdual-hi/src/sdhi` searches these families for groups given by
formulas and prints `SOL ...` only after a full BFS check of the whole graph (both sides). Read the header comment of
`research/selfdual-hi/src/sdhi.c` (group syntax, env variables). Second tool: `research/selfdual-hi/src/haar_sd`
(= research/structured/haar_sym with SDUAL="QOPT U Z0", annealing; header comment of haar_sd.c).

**What we know already (do not repeat).**
- D = 7, SL/PGL(2,q) x Z_n: self-dual involution families are far worse than orbit-symmetric S (k = 3, haar_sym):
  SL(2,5) x Z37 at (6,7): orbit k=3 solves in 2,801 evals, every self-dual psi stalls at 39-622 after 9.5M evals.
  (5,7): self-dual solutions exist up to N = 1,320 (PGL(2,5) x Z11, SL(2,5) x Z11) but not at 1,440 or 1,560.
- psi = inversion with e in S is structurally hopeless (the graph is a double cover of a degree-(K-1) Cayley graph).
- (5,8) record group C61:C80 (r = 8): best family so far is PSI 3 of `sdhi 5 8 meta 61 80 8 cyc 1` (beta(y) = y^41,
  u0 = y^20 central, e not in S), type 1+2+2: best 6 uncovered after 30 s of tabu (full enumeration running).

**Machine rules.** About 4 cores and 15 GB are shared by 9 workers: THREADS=1; run anything heavy as
`timeout 900 nice -n 10 <cmd>`; at most about 1.5 GB of memory; no git commits; write only inside your card folder
`research/squads/sdhi-r1/<card>/` (you may copy tools there). Time box: about 15 minutes of wall clock in total.

**Scorer.** sdhi's own `SOL` lines are already full checks; for any SOL you claim valid also run
`python3 research/selfdual-hi/src/build_sdhi.py D "FACTOR1" "FACTOR2" "S" out.edges` (prints RESULT VALID/INVALID)
and `research/selfdual-hi/src/apsp out.edges K D` (RESULT VALID). Score = smallest "best" (uncovered count) seen at a
group order N that beats the target, or 0 with valid = true for a checked solution.

**Report.** Append ONE line of JSON to `research/squads/sdhi-r1/scoreboard.jsonl`:
`{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <best>, "N": <order>,
"group": "<sdhi factors>", "valid": true|false, "next": "<one line>"}` and reply in at most 5 lines.

## Cards

- **c1** (5,8), beat 9,760 (N >= 4,881). Metacyclic C_p : C_k, p prime, from `research/selfdual-hi/logs/K5D8/meta_p_4881_5100.txt`
  (columns N m k r d inv), the D = 5 record shape. For each group in order: `ENUM=1 ECAP=3000000 NEAR=30 SECS=20 TYPES=1+2+2
  timeout 300 nice -n 10 research/selfdual-hi/src/sdhi 5 8 meta m k r cyc 1`. Note which PSI (beta, u0) gives the
  lowest best; prefer psi with u0 != (0,0). Cover as many groups as you can.
- **c2** (5,8), beat 9,760. Metacyclic groups with composite m and at most 1 involution, d >= 4, from
  `research/selfdual-hi/logs/K5D8/meta_4881_5100.txt` (columns N m k r d inv; filter m not prime, inv <= 1, d >= 4).
  Same command as c1 but with all types (drop TYPES).
- **c3** (5,8), beat 9,760. Direct products Q x H with Q in {psl 3 (A4), sl 3, pgl 3 (S4), sl 4 (A5), sl 5, pgl 5,
  psl 7, sl 7} and H = cyc n or a small metacyclic `meta m k r` (list them with `python3 research/selfdual-hi/src/meta_list.py LO HI`)
  so that |Q| |H| is in 4,881-5,100. `SECS=30 timeout 600 nice -n 10 research/selfdual-hi/src/sdhi 5 8 <Q> <H>` (tabu over every psi and type).
- **c4** (5,8), beat 9,760. Deep tabu on the shape of the record group: C61:C_k (k = 81..84), C41:C120, C31:C160, C71:C70,
  C101:C50, C89:C55 (every r with ord(r) >= 3 dividing k; list with meta_list.py and grep). For each: first
  `LIST=1` to see the psi options, then `SECS=120 STALL=2000 TYPES=1+2+2,1+1+1+2` on the psi options with u0 != (0,0).
- **c5** (6,8), beat 31,680 (N >= 15,841). Self-dual annealing with haar_sd at even D:
  `ORBIT="2 3 0" SDUAL="tw 1 0" THREADS=1 timeout 300 nice -n 10 research/selfdual-hi/src/haar_sd 6 8 240 SEED 8 out.txt <GROUP> <n>`
  (haar_sym group syntax: `psl 11 25`, `sl 5 133`, `psl 7 97`, `sl 7 49` ...) with SDUAL options inv/tw/ninv/ntw and
  U in {1, -1 mod n}; compare with plain orbit search `ORBIT="3 2 0"` (research/structured/haar_sym, build it into your folder:
  `gcc -O3 -march=native -fopenmp -o haar_sym research/structured/haar_sym.c -lm`) on the same groups. Report whether any
  self-dual variant beats the orbit search on any group.
- **c6** (7,8), beat 95,760 (N >= 47,881). Same as c5 at K = 7: `ORBIT="2 3 1"` (e + 3 psi-pairs) with SDUAL tw/inv on
  psl 19 14 (record group, calibration: does it solve?), psl 17 19, then groups of order 47,881-49,000.
- **c7** wildcard. Find an approach none of the other cards uses for any of (5,7) beat 3,120, (5,8) beat 9,760,
  (6,8) beat 31,680, staying within self-dual / bipartite Cayley graphs (for example psi of higher order via ORDS=4,6,
  other group families such as Q1 x Q2 with both factors non-abelian, a different energy or move rule in a copy of
  sdhi.c). Other cards: c1 metacyclic C_p:C_k at (5,8); c2 composite metacyclic at (5,8); c3 Q x H products at (5,8);
  c4 deep tabu near the record shape; c5 haar_sd at (6,8); c6 haar_sd at (7,8); c8 (5,7) metacyclic.
- **c8** (5,7), beat 3,120 (N >= 1,561). The D = 5 record shape at D = 7: metacyclic C_p : C_k with p prime, d = ord(r) >= 3,
  from `research/selfdual-hi/logs/K5D7/meta_1561_1760.txt` (columns N m k r d inv; filter m prime), psi with u0 != (0,0):
  `ENUM=1 ECAP=3000000 NEAR=30 SECS=20 timeout 300 nice -n 10 research/selfdual-hi/src/sdhi 5 7 meta m k r cyc 1`.
