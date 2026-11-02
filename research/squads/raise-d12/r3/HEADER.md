# raise-d12 squad, round 3: shared rules (read this first, then your card)

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
2 free 3-orbits, mu 10.2); (7,12) **59,838,504** (PSL(2,67) x Z199, mu 14.3); (8,12) **297,777,408**, (9,12) **1,178,527,488**, (10,12) **3,888,487,944** (all NEW this job: field-automorphism orbits).
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

## Round 2 of this job (r2/scoreboard.jsonl): all 11 cards negative
- Every new orbit family for (3..7,12) hit a wall: F_512 x| C73 orbit sets take only 22/40/61/62 holes (b01); F_32768 x|
  C151 and SL(2,32) x Z151 floor at exactly 3 clumps (b02, director: 60,000 samples, every batch min 15); D7^5 Haar
  graphs are always disconnected (b05, proof); D17^3, SL(2,8) x D37, SL(2,32) x (Z191 x| Z5) hit abelian or parity
  sections (b06, b10, b07); 54 affine groups F_q x| C_k exhaustively for cubic graphs, best cost 27 (b04).
- So this round goes back to the one small-cell method with a record: own-small's joint base+voltage annealing of 4+4
  cubic lifts plus an exact two-move polish ((3,12) 2,368 = lift over SmallGroup(296,3)), now with real CPU. Round-1
  card a04 tried it but got only ~10^4 iterations per group (best 12-62); own-small reached cost 2 then polished to 0,
  and saw cost 4 at order 294 and cost 8 at order 300.

## Round 1 of this job (r1/scoreboard.jsonl): what we learned
- **Director's find: (8,12) 297,777,408 (+4.8 %), VALID.** G = SL(2,128) x Z71, alpha = (field automorphism x -> x^2 of
  GF(128), order 7) x (z -> 20 z), S = {e} + ONE alpha-orbit of size 7. |Fix(alpha)| = 6 (SL(2,2) x {0}). Plain random
  sampling of the orbit representative: 3 of 420 samples had cost 0 at size-law mu 28 (mu/7 = 4). Tool: haar_bigq (below).
  Large odd k + tiny fixed set + SMALL abelian part is what works.
- **The abelian-quotient wall (a05, a10, a13, a14; read r1/a05 and r1/a14 NOTE/scoreboard lines):** the Z_n coordinate
  (more generally the image in G/[G,G]) of a word depends only on its signed letter counts. With an orbit-closed S the
  letters have few distinct z-values, so words of length <= 11 reach only a bounded number of residues (one 3-orbit at
  Δ = 4: ~199 residues; a 7-letter set: C_11 = 65,226 vectors). If n (or |G/[G,G]|) is not far below that, most of G is
  unreachable: SL(2,8) x Z73 (min cost 61 over all 12,262 orbits), SL(2,8) x Z1063 (82 % uncovered), SL(2,8) x Z59417,
  SL(2,32) x Z941 at (7,12) (director: min 395 vs mu 22). Keep |G/[G,G]| small (n <~ 300 for k = 5, 7 orbits).
- Class-2 nilpotent groups with fixed-point-free order-3 automorphisms (Heisenberg x A) collapse (a13): the orbit lies in
  one line of G/Phi. Frobenius cost-1 states at (6,12) are true local minima (a09). (6,12) SL(2,32) x Z151 with one
  5-orbit floors at 3 clumps (cost 15) over ~10^4 samples and annealing (director, a07).
- Lifts of Moore-graph bases stall far below the values: Tutte 12-cage (H(2) incidence graph) lifts reach only m = 11
  (1,386 vertices; a01: exactly 65 non-backtracking walks of length <= 12 from a vertex to each line, and they are the
  geodesic plus apartment detours), W(3) lifts at (4,12) stay at cost 350-450 (a16). Order-5 CONJUGATION orbits in
  PSL(2,p) are bad (a08: min cost 184 at (6,12), Fix ~ p/2); only field automorphisms (tiny Fix) worked.
- Open leads: a13's F_512 x| C_73 (Frobenius group, kernel F_2^9, alpha = Frobenius x -> x^8 of order 3, Fix = F_8,
  N = 37,376 -> 74,752 at (4,12)): random S reached 17 holes in 300 tries; the orbit scan was running.

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
- `$B/haar_bigq d D secs seed K OUT sl|psl q n` (NEW, director): haar_big0 for SL/PSL(2,q) x Z_n with q = p^e (any
  prime power <= 4096), N/2 bytes of memory, bit-parallel; env ORBIT, AFROB=j (field automorphism orbits), FIXORD=o
  (alpha-fixed generators of order o), RANDORB=m (writes OUT on a cost-0 sample), START, EVAL, UNCPRINT, THREADS.
  Needs gcd(|T|, n) = 1 with |T| = q-1 (sl) or (q-1)/2 (psl). Source research/frontier/raise-d12/haar_bigq.c.
  Example (the (8,12) find): `ORBIT="7 1 1" AFROB=1 RANDORB=100 THREADS=1 $B/haar_bigq 8 12 100 2 4 OUT sl 128 71`.
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

## Machine rules (4 cores and 15 GB; this round has 6 cards and ~2-3 free cores, so each card gets real CPU)
- Every heavy command: `timeout 105 nice -n 10 <cmd>` with THREADS=1 and secs <= 100. **Never start a command that
  runs longer than 110 s** (a longer command goes to the background and you sit idle). Chain runs instead (save the best
  state, restart from it with a new seed).
- One process at a time. **Memory cap: 400 MB per card** (the director's searches hold ~6 GB).
  Estimate before running (haar_sym ~18 bytes per element; bitsets 1 bit per element per set; tables d x 4 bytes per row).
- Runs are 2-5x slower than on an idle machine (16 cards on 4 cores). That is expected; plan for it.
- No git commits. Use ONLY the Bash, Read, Write, Edit, Glob and Grep tools. **Never call any session, messaging or
  GitHub tool** (create_session, archive_session, send_message, mcp__*): round-1 cards called two of them by mistake. Append to the scoreboard with `>>` as ONE line of JSON (no line breaks inside); never rewrite or edit it (one round-1 card rewrote the whole file).
- Work only in your folder /home/user/degree-diameter/research/squads/raise-d12/r3/<card>/ (create it).
- Save any valid graph: Haar solution files as written by the tools; other graphs as an edge list (first line n, then
  "u v") plus the apsp output in a .check.txt file next to it.
- **Time box: about 30 minutes of wall time from your first command. Use all of it** (earlier rounds stopped after 5-10
  minutes; that wastes the slot). Then write the scoreboard line and stop.

## Output
Append ONE line of JSON to /home/user/degree-diameter/research/squads/raise-d12/r3/scoreboard.jsonl:
{"card": "cNN", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "cell": "(d,12)",
 "score": <vertex count of your largest diameter-<=12 graph, or 0>, "beats": "<value it beats, or no>",
 "best_cost": <lowest cost reached at your target size>, "valid": "<checker and verdict, or none>",
 "file": "<solution or edge-list path, or none>", "finding": "<one line: what you learned, with numbers>",
 "next": "<one line>"}
Then reply to the director in at most 5 lines.
