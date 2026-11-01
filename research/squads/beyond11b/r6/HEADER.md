# beyond-d11b squad, round 6: shared rules (read this first, then your card)

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
D = 11: (3,11) 1,474; (4,11) **30,334** (round 2, h01: Z_523 x|_9 Z_29); (5,11) **311,426** (round 5, k05: Z5023 x|_2886 Z31); (6,11) **2,122,518** (round 5, k07: Z20809 x|_12972 Z51); (7,11) 11,012,976; (8,11) 45,329,808;
(9,11) 155,250,816; (10,11) 460,691,568; (11,11) 1,241,299,248.
D = 12: (3,12) 2,176; (4,12) **70,176** (round 5, k02: Z731 x|_7 Z48); (5,12) **1,056,886** (round 5, k03: Z8663 x|_43 Z61); (6,12) 9,366,240; (7,12) 59,838,504; (8,12) 284,095,056;
(9,12) 1,105,785,120.
How they were made: (3,11) metacyclic Z67 x|_9 Z11 (odd order 737), (3,12) Z68 x|_3 Z16 (exhaustive pair search); all
others SL(2,p) x Z_n (odd D) or PSL(2,p) x Z_n (even D) with S closed under alpha = (conjugation by a matrix of order 3)
x (z -> r z, r of order 3 mod n), ORBIT "3 m f" (S = f alpha-fixed generators incl. e + m orbits of size 3; f = 0 means
m free orbits, no e). Size law (research/frontier/SIZE_LAW.md): a random S on a group of order N leaves about
mu = N exp(-W/N) elements uncovered (W = number of same-side words); the values above sit at mu ~ 8-15.

## Round 5 of this job (r5/scoreboard.jsonl, r5/k14/NOTE.md)
- Raises from save/resume chains: (5,11) 311,426, (6,11) 2,122,518, (5,12) 1,056,886, (4,12) 70,176 (Z731 x| Z48, composite m).
- **Targeted finisher:** `$B/haar_gen3t` (source tools/haar_gen3t.c, card r5/k13) = haar_gen3s plus TFULL=1: targeted candidate
  moves use full-length walks (with TARGP=100 every candidate targets an uncovered element). It took (4,12) Z677 x| Z52 from cost
  2 to 1 where plain chains stayed at 2-3. PAIRP / LOCALP moves are useless (do not use). Use: `START=best.txt SAVEBEST=b2.txt
  TFULL=1 TARGP=100 THREADS=1 timeout 105 nice -n 10 $B/haar_gen3t d D 90 <seed> 4 OUT <spec> 1`.
- k14: at odd D the holes of a Frobenius group come in inverse pairs on one side (cost 4 = one pair per side); at (4,12) the last
  hole of a cost-1 state was an involution (k = 52 even).
- Best states to finish (cost): (4,12) Z677 x| Z52 r5/k01/best_c677b7.txt, r5/k13/s677_tfull*.txt, r5/k14/c11.best.txt (1);
  (6,12) Z74719 x| Z63 r5/k10/*.best (1); (5,12) Z8969 x| Z59 (N 529,171) r5/k03/s_c308c.txt (1-2); (7,11) Z100981 x| Z55
  (N 5,553,955) r5/k12/c100981k55b.best.txt (2), Z90281 x| Z61 r5/k11/s21.txt (2); (6,11) Z24683 x| Z43 (N 1,061,369, r5/k07) (2);
  (5,11) (Z7 x| Z3) x (Z173 x| Z43) r5/k04 (2), Z3061 x| Z51 and Z2861 x| Z55 r5/k06 (4).

## Round 4 of this job (r4/scoreboard.jsonl)
- Raises: (6,11) 2,112,114 (Z20707 x| Z51, 2 seeds of 7), (5,12) 1,050,906 (Z10303 x| Z51), (5,11) 310,718 (Z3613 x| Z43).
- **Save/resume now exists:** `$B/haar_gen3s` (source tools/haar_gen3s.c, card r4/j14): same CLI as haar_gen3, plus
  SAVEBEST=<file> (writes the best S at every improvement, any cost) and START=<file> (resume from such a file; same
  group spec). Chain: `SAVEBEST=b.txt ... ; START=b.txt SAVEBEST=b2.txt ...`. j14: chaining reached cost 4 where one run
  reached 8 on (5,11) Z8209 x| Z19, then stalled at 4 for 6 links.
- Near misses: (4,12) Z677 x| Z52 (N = 35,204) cost 2, Z701 x| Z50 cost 2-3; (5,12) Z11701 x| Z45 (526,545), Z8663 x| Z61
  (528,443), Z8969 x| Z59 (529,171) cost 1-2; (5,11) (Z7 x| Z3) x (Z173 x| Z43) (156,219) cost 2, Z5023 x| Z31 (155,713)
  cost 2, Z4481 x| Z35 cost 4-6; (6,11) k = 33 N = 1,058,541 cost 4; (6,12) Z74719 x| Z63 (4,707,297) cost 2;
  (7,11) Z90281 x| Z61 cost 2 (2 of 13 seeds), Z90647 x| Z61 cost 4.
- Dead: (4,11) above N = 15,167 (k = 13-33 groups plateau at 4-12 over ~40 runs).

## Round 3 of this job (r3/scoreboard.jsonl)
- Frobenius groups and odd products raised (6,11) (2,098,038 and 2,095,758), (4,12) (70,038 in 2 s), (5,12) (1,045,054).
- Near misses (cost 1-2) to farm with many seeds: (4,12) Z701 x| Z50 (N = 35,050) cost 1; (5,12) Z8317 x| Z63 (N = 523,971)
  cost 1; (5,11) Z6763 x| Z23 (155,549) and Z5023 x| Z31 (155,713) cost 2, (Z7 x| Z3) x (Z173 x| Z43) (156,219) and
  Z8209 x| Z19 (155,971) cost 4; (6,11) products near N = 1,050,063 cost 2, Frobenius k = 61 (1,049,383), k = 51
  (1,056,057) cost 2; (7,11) Z90281 x| Z61 (N = 5,507,141) cost 2.
- Dead ends: (4,11) Z463 x| Z33 (15 seeds, 4-6); composite k and p^2 kernels; (8,11), (7,12) too slow for cards.

## Round 2 of this job (r2/scoreboard.jsonl, r2/h13/NOTE.md, r2/h17/NOTE.md)
- Plain random S (haar_gen3, no ORBIT) on Frobenius groups Z_p x| Z_k (p prime, k odd, k | p-1, r of order k) raised
  (4,11) to 30,334 (Z523 x| Z29, N = 15,167, solved in 28-45 s, 2 seeds of 2), (5,11) to 310,498 (Z8171 x| Z19) and
  306,182 (Z5279 x| Z29), (4,12) to 68,906 (Z263 x| Z131, 1 seed of 5). Solve rates per seed are ~1/5 near the limit:
  **run many seeds (K = 4 and 8), 60-100 s each, rather than one long run.**
- k matters: k = 3 collapses (1 + r + r^2 = 0), k = 7-15 much worse than k = 19-35 at (4,11)/(5,11) (h13: Frobenius
  k = 13/19 have random-like middle levels, X_8/model 0.99, while SL(2,23), SL(2,13) x Z7 lose 8-11 %); h17: balanced
  C_k labels of S (no label class too large, >= 3 distinct labels) predict fewer holes.
- haar_gen3 is fast only if G has a cyclic subgroup of order 2..63 to use as H: for Z_p x| Z_k use k <= 63 (or k with a
  divisor in 2..63); k = 131 or 181 ran at ~50 evals/s (H order 1).
- Did not work: ORBIT with the scaling automorphism AMU (orbits in one C_k slice; h10), ORBIT "3 1 1" (conjugation) on
  Frobenius groups, SL(2,q) x F at (5,11)/(6,11) beyond g16's (cost 4-18), SL(2,103) x H21 at (8,11) (cost 14), 2-dim
  Frobenius Z_p^2 x| Z_k (25,230 at (4,11)), cubic Frobenius (exh3: cost >= 84), cubic lifts (cost 2 at 2,184).
- Near misses to resume: (6,11) (Z67 x| Z3) x (Z307 x| Z17), N = 1,049,019, cost 2 (r2/h15); (6,11) SL(2,7) x (Z449 x| Z7)
  cost 2-4; (4,11) Z421 x| Z35 (N = 14,735) and Z1321 x| Z11, Z541 x| Z27 cost 2; (5,11) Z8209 x| Z19 cost 4;
  (5,12) Z2897 x| Z181 cost 8; (7,11) Frobenius k = 23 (N = 5.5M) cost 18; (6,11) Frobenius k = 63 (N = 1,047,879 and
  1,055,817) cost 2 on 4 seeds, k = 39 cost 2-6 (r2/h06/groups.txt lists 240 groups).

## Round 1 of this job (research/squads/beyond11b/r6/scoreboard.jsonl; read the lines of the cards you build on)
- **Odd-order, centre-free Frobenius groups beat the size law at odd D.** g02: Z_761 x|_25 Z_19 (order 14,459, Frobenius:
  761 prime, k = 19 odd, r of order 19 mod 761), plain random S with haar_gen3, (4,11) 28,918 vertices at size-law mu 31.6
  (SL/PSL groups stall near mu 10-15); N = 12,181 and 14,209 solved in seconds, 14,531-15,025 stopped at cost 2-4 in 95 s.
  g16: SL(2,5) x (Z_37 x|_10 Z_3) (4,11) 26,640 in 0.2 s at mu 17; SL(2,5) x (Z_251 x|_20 Z_5) (5,11) 301,200 at mu 14;
  (6,11) SL(2,7) x (Z_449 x| Z_7) reached cost 2. Spec syntax: `meta p k r`, `prod sl 5 meta 251 5 20`, then n = 1.
- Negatives: odd-order meta groups WITH a centre or composite m (g03, (5,11): start costs 1e3-2.6e5, best plateau 4-14);
  F_q x| C_k with q = 37^3, k = 21 (g04: ~10x worse than the size law); Sz(8) (g13); bipartite Cayley graphs of PGL(2,p)
  (g06, worse than Haar); SL(2,p^e) with Frobenius alpha (g05: better start costs than conjugation, plateau 10); PSL(2,p^e)
  at even D (g08, plateau 5); voltage lifts of PG(2,3) (g12: 19,500 at (4,11)); ORBIT "3 1 1" (conjugation alpha) on
  SL(2,5) x Frobenius hurt (g16: cost 222 vs 242 plain start, no solve); products of agl1 groups (g11, plateaus 8-11).
- Theory (g15, r1/g15/NOTE.md): with f = 0, n_h(-I) = 0 mod 6; spending a pair (s, -s) on -I is bad.

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
- One process at a time. **Memory cap: 150 MB per card** unless your card says otherwise (the director's checks need
  11 GB; going over can kill a 40-minute check). haar_big0 prints its own memory estimate on line 1 (about N/2 bytes);
  for other programs estimate before running (a byte per element per bitset, tables N/nH*d*4 bytes, etc.).
- The director's checks run at nice -5 and yours at nice 10, so runs can be 2-5x slower than quoted. That is expected.
- No git commits. Use only the shell and file tools: never call session, messaging or GitHub tools (create_session,
  send_message, mcp__*). Append to the scoreboard with `>>` as ONE line of JSON (no line breaks inside); never rewrite the file.
- Work only in your folder /home/user/degree-diameter/research/squads/beyond11b/r6/<card>/.
- **Memory cap: 150 MB per card in round 6** unless the card says otherwise (the director's 30-billion checks hold 11 GB).
- haar_gen3 / haar_sym on a meta group: tables are about N/nH x d x 4 bytes plus a few N-bit bitsets; fine up to N ~ 3e7.
- **Time box: about 25 minutes of wall time from your first command. Use all of it** (earlier rounds stopped after 5-10
  minutes; that wastes the slot). Then write the scoreboard line and stop.

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/beyond11b/r6/scoreboard.jsonl:
{"card": "lNN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,D)",
 "score": <vertex count of your largest diameter-<=D graph, or 0>, "beats": "<value it beats, or no>",
 "valid": "<checker and verdict, or none>", "file": "<solution or edge-list path, or none>",
 "finding": "<one line: what you learned, with numbers>", "next": "<one line>"}
Then reply to the director in at most 5 lines.
