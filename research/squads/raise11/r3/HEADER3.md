# raise-d11 squad: shared rules (read this first, then your card)

Job raise-d11 (2026-11-01/02, Opus director, branch claude/raise-d11-frontier-26r11l). Problem: bipartite
degree-diameter, the largest Δ-regular bipartite graph of diameter D. **Goal of the job: raise our D = 11 values,
mainly Δ = 6..10 for squad cards.** Values come from Haar graphs H(G,S): vertices (g,A),(g,B), g in G, edges
(g,A)~(s g,B), s in S, |S| = Δ; 2|G| vertices. Right multiplication by G is transitive on each side, so BFS from (e,A)
and from (e,B) gives the exact diameter. Odd D = 2h+1 needs BOTH (S^-1 S)^h = G and (S S^-1)^h = G.

## Values to beat at D = 11 (vertices, all checked; N = |G| = vertices / 2)
(3,11) 1,474 · (4,11) 30,334 · (5,11) 311,426 · **(6,11) 2,122,518** (Frobenius Z20809 x|_12972 Z51, N 1,061,259, mu 10.7)
· **(7,11) 11,012,976** (SL(2,53) x Z37, N 5,506,488, mu 10.4) · **(8,11) 45,329,808** (SL(2,283), N 22,664,904, mu 11.0)
· **(9,11) 155,250,816** (SL(2,223) x Z7, N 77,625,408, mu 10.6) · **(10,11) 460,691,568** (SL(2,613), N 230,345,784,
mu 9.3) · (11,11) 1,241,299,248 · (12,11) 2,976,066,240 · (13,11) 6,781,213,392 · (14,11) 14,381,398,080.
mu = N exp(-W/N) is the size-law expected number of uncovered elements per side (W = same-side words of length <= 10);
solves were found at mu ~10. **A +1 % raise needs mu ~12.5-14, +2 % needs mu ~15.** Searches need about e^(mu/2) times
more work per +1 in mu, so many independent seeds (lineages) beat one long run.

## Already found / already ruled out (do not repeat)
- SL(2,p) x Z_n with S closed under alpha = (conjugation by g of order 3) x (z -> r z, r of order 3 mod n), ORBIT "3 m f"
  (f alpha-fixed generators incl. e, m orbits of size 3; f = 0: m free orbits, no e) is the standard for Δ >= 7. Odd D:
  prefer SL with small n (PSL has ~p^2/2 involutions, each missed with prob ~exp(-lambda/2); central elements (2n of them)
  ~exp(-lambda/5); alpha-fixed torus elements (~p) ~exp(-lambda/3)): research/frontier/beyond11/ODD_D_HOLES.md.
- Frobenius groups Z_q x|_r Z_k (q prime, k odd, k | q-1, r of order k) with plain random S raised Δ = 4, 5, 6
  (research/frontier/beyond11/FROBENIUS.md). Prime k in 19..61 is best; k = 3, 7 bad; composite k, 2-dim kernels,
  orbits on Frobenius groups (labels are preserved, so orbits degenerate), SL x Frobenius products beyond Δ = 5: worse.
- Ruled out at D = 11: orbit sizes k = 2, 4, 5, 6; self-dual transpose-closed S; -I as a generator; annealing knob tuning
  (K, TARGP, BOUNDCUR) at (11,9); meet-in-the-middle near-miss finisher; exhaustive 1-swap finishing of cost-1/2 states
  (they are true local minima; solves come from fresh lineages). **New today (director):** inverse-closed S (S = S^-1,
  one side to cover): with e in S the words collapse (u e u^-1 = e), 10^5-10^6 holes; without e (even Δ) per-side holes
  double, so the number of independent hole clumps is about the same as the standard; no gain shown yet (card c12 tests
  solve rates).
- Near misses from earlier jobs: (7,11) Z90281 x| Z61 (N 5,507,141) and Z100981 x| Z55 (N 5,553,955) cost 2 (slow tool).

## Tools (absolute paths; build nothing new unless your card says so)
B=/home/user/degree-diameter/research/squads/raise11/bin
- `$B/haar_big0 d D seconds seed K OUT sl|psl p n` with env ORBIT="3 m f" (d = f + 3m), THREADS=1. Annealing over orbit
  slots; prints "t=.. step=.. evals=.. cost=.. best=..", a final "RESULT ... best=B evals=E ...". The best S so far is
  written to OUT.best (f = 0: also OUT.best.orb, the orbit form); on cost 0 it re-evaluates and writes OUT.
  Resume: START=OUT.best (f >= 1) or START=OUT.best.orb (f = 0). Stats only: RANDORB=m (m random symmetric S, prints
  min/median). Re-evaluate a file: EVAL=file (prints cost; UNCPRINT=1 lists up to 200 uncovered elements, "(B side)"
  marks holes of the second side). Source: research/frontier/beyond11/haar_big0.c (read its header comment).
- `$B/haar_sd`: haar_big0 plus SYM=1 (inverse-closed slots: ORBIT "6 m f" = alpha-orbit + inverses, or "2 m f" = pairs
  {x, x^-1}; cost = holes of ONE side). Use f = 0 (no e) only. Source research/frontier/raise11/haar_sd.c.
- `$B/haar_gen3s` / `$B/haar_gen3t` (Frobenius and other families, plain random S): `haar_gen3s d D seconds seed K OUT meta q k r 1`
  with SAVEBEST=file (best state, any cost) and START=file (resume); haar_gen3t adds TFULL=1 TARGP=100 (targeted
  finisher). Sources research/squads/beyond11b/tools/.
- `python3 $B/pick11.py d lo hi [sl|psl|meta|all] [nmax]`: groups with lo*N_rec < N <= hi*N_rec, with mu and gain;
  meta lines give "q k r" for haar_gen3s.
- Checkers (the director re-checks every find independently; you may run them if they fit in 105 s):
  `OMP_NUM_THREADS=1 $B/haarcheck_gen SOL` (SL/PSL; prints VALID/INVALID), `python3 /home/user/degree-diameter/research/frontier/build_haar2.py SOL` (any family, N <= ~5e6).

## Machine rules (4 cores and 15 GB shared by 16 cards and the director)
- Every heavy command: `THREADS=1 timeout 105 nice -n 10 <cmd>` (seconds argument <= 95). **No command may run longer
  than 110 s**: a longer command goes to the background and you sit idle. Chain runs instead (resume with START=).
- At most 1.5 GB of memory per process; one heavy process at a time per card.
- Work only in your folder /home/user/degree-diameter/research/squads/raise11/r3/<card>/ (create it). No git commands,
  no edits outside your folder, no other subagents, no session/messaging/scheduling/remote tools of any kind.
- Time box: about 25 minutes of work, then report.

## Report
1. Append ONE line of JSON to /home/user/degree-diameter/research/squads/raise11/r3/scoreboard.jsonl (single line; use
   python3 -c 'import json; print(json.dumps({...}))' >> file to get valid JSON):
   {"card": "c05", "cell": "(8,11)", "idea": "<one line>", "group": "<spec of best run>", "N": <N of best state>,
    "best_cost": <lowest cost reached at that N>, "vertices_if_solved": <2N or 0>, "beats_record": true|false,
    "file": "<path of the cost-0 solution or best state>", "command": "<exact command>", "evals": <total>,
    "finding": "<one line: what you learned>", "next": "<one line>"}
2. Reply to the director in at most 5 lines: best result, file path, the one thing you learned.

## ROUND 2 (read this; it overrides the values above)
**Round 1 found the lever:** SL(2,p) x Z_n (or PSL) with SMALL n and the standard ORBIT shape solves far above the old
mu ~10 wall: (8,11) SL(2,149) x Z7 at mu 15.3 (+2.16 %, card c06, 1 of ~3 fresh runs), (7,11) PSL(2,47) x Z109 at mu 15.2
(+2.71 %, c04), (10,11) SL(2,151) x Z67 (+0.14 %, c08, fresh seed in 29 evaluations), (12,11) SL(2,601) x Z7 (+2.12 %,
director, 5 evaluations), (6,11) Frobenius Z25913 x| Z41 (+0.11 %, c01). Card c13's clump model ranks groups:
K = expected number of independent hole clumps, P(cost 0 per fresh run) ~ exp(-K) (research/squads/raise11/r1/c13/MODEL.md;
it over-penalises large n: c04 solved at model K = 17). **Fresh seeds beat resumes** (c08, c16, c07): chains stall
at cost 2-6; a new seed is the better use of 95 s.
**New values to beat (vertices):** (5,11) 311,426 · (6,11) 2,124,866 · (7,11) 11,311,584 · (8,11) 46,309,200 ·
(9,11) 155,250,816 · (10,11) 461,335,200 · (11,11) 1,241,299,248.
Ruled out in round 1: inverse-closed S (c12: 8-10x worse), more alpha-fixed generators (f >= 4: 10^6 holes, c11, c14;
keep the standard f: Δ=7 "3 2 1", 8 "3 2 2", 9 "3 3 0", 10 "3 3 1", 11 "3 3 2", 6 "3 2 0", 5 "3 1 2"), large n
(central holes (+-I, z) are 25-30 % of the holes at n >= 229, c09), other families at (7,11) (c15: PGL, SL(2,49), AGL1 worse).

## The LADDER protocol (all round-2 search cards)
Your card lists rungs (groups) in increasing size. Work on the first rung that beats the CURRENT value of your cell. Run
fresh seeds (95 s each, new seed every run; resume a state only once if it reaches cost <= 2). When a rung solves
(RESULT ... best=0 and "wrote OUT"): (1) append a scoreboard line for it at once, (2) run the checker if your N <= 3e7:
`OMP_NUM_THREADS=1 timeout 105 $B/haarcheck_gen OUT` (SL/PSL) or `timeout 105 $B/metacheck OUT` (meta), note VALID in
the line, (3) move to the next rung. You may append one scoreboard line per solve (plus one final line).
New tool: `$B/haar_meta d D seconds seed K OUT q k r` = haar_big0's fast engine for Frobenius groups Z_q x|_r Z_k with
plain random S (no ORBIT needed; resume with START=OUT.best); 2 ms per evaluation at N = 1e6, ~10x faster than haar_gen3s.
Checker for meta files: `$B/metacheck OUT` (VALID/INVALID).
**Hard rules (repeated because round-1 cards broke them):** never call any mcp__claude-code-remote tool or any
session, messaging, archive, interrupt or scheduling tool; no process above 1 GB of memory (the director needs the rest
for a 12 GB check); `THREADS=1 timeout 105` on every heavy command.

## ROUND 3 (overrides the values above)
Values to beat now: (5,11) 311,426 · (6,11) **2,135,280** (PSL(2,41) x Z31, r2/e09) · (7,11) 11,311,584 · (8,11) 46,309,200
· (9,11) 155,250,816. Cells Δ >= 10 are run by the director (the box is too loaded for cards there: r2/e07, e08 got
2.5-28 s per evaluation). Round 2: the ladders' first rungs reached cost 4-8 at (7,11) sl 67 19, (10,11) sl 617 1 and
sl 263 13, (8,11) sl 107 19 (8); cost 18 at psl 53 79 and sl 151 7; pure random sampling is worse than annealing (e13).
**Each card now owns ONE group** (no ladder): run as many fresh 95-s seeds as you can (one per command, new seed each time),
and resume only states at cost <= 2 (once). A solve is reported and checked as in the ladder protocol, then continue
with fresh seeds on the next group your card names, if any.
