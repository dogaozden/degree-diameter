# raise-d12 squad, round 1: shared rules (read this first, then your card)

Job raise-d12 (2026-11-01/02, Opus director, branch claude/d12-frontier-cells-m24ikx). Problem: bipartite
degree-diameter: the largest bipartite graph of maximum degree Δ and diameter D. This job: **raise the D = 12 values**.
Most values come from Haar graphs H(G,S): vertices (g,A),(g,B), g in G, edges (g,A)~(s g,B), s in S, |S| = Δ; 2|G|
vertices. Right multiplication by G is transitive on each side, so for even D one BFS from (e,A) decides the diameter:
every B-element within D-1 of (e,A) => diameter <= D. Size law (research/frontier/SIZE_LAW.md): a random S on a group
of order N leaves about mu = N exp(-W/N) elements uncovered, W = sum over odd j <= D-1 of Δ(Δ-1)^(j-1); the search
solves when mu is small (~5-15). Orbit-closed S (S invariant under an automorphism alpha of order k) makes holes come
in clumps of k, so a valid S appears with probability ~exp(-mu/k - (fixed-point term)) instead of exp(-mu)
(research/theory/BEYOND_RANDOM.md on branch claude/cd-theory-beyond-random-3ybyf2: odd k only; small Fix(alpha) needed).

**Your job: raise one D = 12 cell with an idea that has NOT been tried, or produce a clear negative with numbers.**
A new structure that works is worth more than a 0.5 % raise by an old method.

## Values to beat (vertices; all checked)
(3,12) **2,368** (4+4 voltage lift over SmallGroup(296,3) = Z37 x|_6 Z8, job own-small); (4,12) **70,176** (Haar, Z731 x|_7 Z48,
random S); (5,12) **1,058,342** (Haar, Frobenius Z8969 x|_205 Z59, random S); (6,12) **9,366,240** (Haar PSL(2,79) x Z19,
2 free 3-orbits, mu 10.2); (7,12) **59,838,504** (PSL(2,67) x Z199, mu 14.3); (8,12) 284,095,056; (9,12) 1,105,785,120.
Upper bound M_b - 6 (M_b = bipartite Moore bound); (3,12) <= 8,184.

## Already found or ruled out (do NOT redo)
- Random S (no orbits) on SL/PSL(2,p) x Z_n and on Frobenius groups Z_p x|_r Z_k (p prime, k | p-1): pushed to cost-1/2
  local minima at (4,12), (5,12), (6,12) by job beyond-d11b (6 squad rounds, save/resume chains, targeted finisher
  haar_gen3t; an exhaustive scan of all single-generator swaps of a cost-1 (4,12) state found no cost 0). Details:
  research/frontier/beyond11/FROBENIUS.md. Do not just rerun these chains (card a09 is the only finisher card).
- Conjugation orbits k = 3 on SL/PSL(2,p) x Z_n: the current (6..12,12) values; plateaus at cost 1-3 for thousands of
  evaluations at (6,12) PSL(2,211), (9,12) PSL(2,167) x Z241, PSL(2,331) x Z31.
- k = 2 and 4 orbits (even k: forced word coincidences); field automorphism with k = 2, 3 at small fields (beyond-d11b g05,
  g08: (5,12) PSL(2,49) x Z9 k = 2 cost 5; (6,12) PSL(2,125) x Z5 k = 3 cost 9-12); automorphism orbits on Frobenius
  groups (scaling a -> u a degenerates); Sz(8); PGL(2,p) bipartite Cayley graphs; 2-dimensional kernels Z_p^2 x| Z_k at
  Δ = 4, 5; F_{p^3} x| C_k.
- Cubic (3,12): exhaustive pair search over every metacyclic Z_m x|_r Z_k of order 931-1,728 (best 2,176), Frobenius and
  product groups (exh3, cost >= 84), lifts of cubic multigraphs (cost 2 at 2,184); census graphs: CSS(2304,5) has
  diameter 12 (not ours).
- Director's probe (this job): (6,12) SL(2,32) x Z151 with the field automorphism of order 5 ("5 1 1", AFROB=1,
  N = 4,943,136 -> 9,886,272, mu 21.5): 1,500 random symmetric S: min cost 15 (3 clumps), median 172; 100 s of annealing
  (4,745 evaluations): best 20. Not solved yet (card a07 continues this).

## Tools (absolute paths, already built; do not rebuild them, copy the source if you need a variant)
B = /home/user/degree-diameter/research/squads/raise-d12/bin
- `$B/haar_sym d D secs seed K OUT GROUP... n`: annealing Haar search over haar_gen3's families (meta m k r, sl q, psl q,
  pgl q with q a prime or prime power (field printed as "poly ..."), agl1 q, prod G1 G2, cyc, heis q) x Z_n. Env
  ORBIT="k m f" (S = {e} + (f-1) alpha-fixed + m orbits of size k; f = 0: m free orbits, no e), AFROB=j (alpha = field
  automorphism x -> x^(p^j) on GF(p^e), order e/gcd(e,j)), AR=<r> (z -> r z), RANDORB=m (statistics of m random symmetric
  S; writes OUT if one has cost 0), THREADS=1, FAST=0 (less memory). Source and options: research/structured/haar_sym.c
  (header) and research/structured/README.md. Writes OUT only on cost 0. Memory ~14-18 bytes per group element.
- `$B/haar_gen3`, `$B/haar_gen3s` (SAVEBEST=, START=), `$B/haar_gen3t` (plus TFULL=1 targeted finisher): random-S
  searches, same CLI without ORBIT (sources research/frontier/haar_gen3.c, research/squads/beyond11b/tools/).
- `$B/haar_big0 d D secs seed K OUT sl|psl p n`: bit-parallel search for SL/PSL(2,p) x Z_n, p prime, N/2 bytes of
  memory, env ORBIT, START, RANDORB, EVAL. Source research/frontier/beyond11/haar_big0.c.
- `$B/exh3 TABLE.bin D [OUTPREFIX]`: exhaustive cubic Haar search over a group table; tables from
  `python3 /home/user/degree-diameter/research/squads/beyond11b/tools/groups.py SPEC OUT.bin` (grammar in its header).
- `$B/hexgen2 q`: the split Cayley hexagon H(q) (q <= 32 prime power) as point/line incidence; writes hex/hex_q{q}.bin in
  the current directory (format in research/d10D7/hexgen2.c header). Its incidence graph has 2(q^6-1)/(q-1) vertices,
  degree q+1, girth 12, diameter 6.
- `$B/salift_s`: own-small's annealer over voltage lifts of cubic p+p base multigraphs (source
  research/squads/own-small/r2/w4/salift_s.c; it reads GAP-exported multiplication tables, so you must write your own
  table for the group; read the source first).
- Checkers (the scorer): `python3 /home/user/degree-diameter/research/frontier/build_haar2.py SOL.txt` for haar_sym /
  haar_gen3 / haar_big0 solution files (only for 2N <= 2,000,000); `OMP_NUM_THREADS=1 $B/haarcheck_gen SOL.txt` (sl/psl
  over GF(q), q = p^e with "poly", and prod; N <= 3e7); `$B/apsp EDGES Δ D` (all-pairs BFS on an edge list: first line
  n, then "u v" lines; n <= 400,000) for any other graph (lifts). A card's "valid" is a claim; the director re-checks.

## Machine rules (4 cores and 15 GB shared by 16 cards and the director's 11 GB check)
- Every heavy command: `timeout 105 nice -n 10 <cmd>` with THREADS=1 and secs <= 100. **Never start a command that
  runs longer than 110 s** (a longer command goes to the background and you sit idle). Chain runs instead (save the best
  state, restart from it with a new seed).
- One process at a time. **Memory cap: 150 MB per card** (the director's check holds 11 GB; going over can kill it).
  Estimate before running (haar_sym ~18 bytes per element; bitsets 1 bit per element per set; tables d x 4 bytes per row).
- Runs are 2-5x slower than on an idle machine (16 cards on 4 cores). That is expected; plan for it.
- No git commits. Use only the shell and file tools: never call session, messaging or GitHub tools (create_session,
  send_message, mcp__*). Append to the scoreboard with `>>` as ONE line of JSON (no line breaks inside); never rewrite it.
- Work only in your folder /home/user/degree-diameter/research/squads/raise-d12/r1/<card>/ (create it).
- Save any valid graph: Haar solution files as written by the tools; other graphs as an edge list (first line n, then
  "u v") plus the apsp output in a .check.txt file next to it.
- **Time box: about 30 minutes of wall time from your first command. Use all of it** (earlier rounds stopped after 5-10
  minutes; that wastes the slot). Then write the scoreboard line and stop.

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/raise-d12/r1/scoreboard.jsonl:
{"card": "aNN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,12)",
 "score": <vertex count of your largest diameter-<=12 graph, or 0>, "beats": "<value it beats, or no>",
 "best_cost": <lowest cost reached at your target size>, "valid": "<checker and verdict, or none>",
 "file": "<solution or edge-list path, or none>", "finding": "<one line: what you learned, with numbers>",
 "next": "<one line>"}
Then reply to the director in at most 5 lines.
