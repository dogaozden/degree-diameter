# deep-65 round 1 cards (Opus-written, 4 Haikus)

## Common rules (every card)
- Goal: a bipartite graph with maximum degree 6 and diameter 5 on MORE than 684 vertices (table value 684).
  Scorer: `score65 EDGES` (bad = unordered vertex pairs at distance > 5; 0 means diameter <= 5), then `apsp EDGES 6 5`.
- Tools: research/squads/deep-65/shared/ (README.md lists them), research/squads/deep-65/tools/hubk.c. Copy what you need
  into your own folder and build there (`gcc -O3 -march=native -o X X.c -lm`). GAP is installed for group tables:
  `gap -q -c 'ORDER:=147; OUTDIR:="groups";' /home/user/degree-diameter/research/squads/deep-65/tools/gap_tables.g`.
- Machine: 4 cores shared with 3 other workers and Opus's exact searches. Single-threaded only. EVERY command must finish
  in under 110 s: wrap heavy runs as `timeout 105 nice -n 10 CMD` and chain several short runs (longer commands get moved
  to the background and you would sit idle). Never start background processes, never `sleep`. At most 1.5 GB memory.
- Work only in your folder research/squads/deep-65/round1/<card>/. No git commands. No edits outside your folder except
  appending to the scoreboard.
- Time box: 70 minutes from your start. Keep NOTES.md in your folder (what you ran, exact commands, results).
- Scoreboard: append ONE JSON line per new best and one at the end to research/squads/deep-65/round1/scoreboard.jsonl:
  {"card": "h1", "idea": "<one line>", "code": "<path>", "command": "<exact>", "n": <vertices>, "score": <bad pairs or cost>,
   "valid": true|false, "next": "<one line>"}
- Final reply to Opus: at most 5 lines.

## h1: lead (a), the 684 graph plus one vertex pair, by design
The 684 graph (shared/h684.edges) is a Haar graph; every edge is critical. Opus measured the damage of deleting one edge
(shared/damage684.c): it is ONLY same-side pairs at distance 4, 44-83 per edge type, all of two kinds: (0,3) pairs (x, v)
with v at distance 3 from y (and the mirror), and (1,2) pairs (u, v) with u ~ x, v at distance 2 from y.
Insertion: delete edges (x_i, y_i), i = 1..5, add a in A and b in B with a ~ b, a ~ y_i, b ~ x_i (n = 686, all degrees 6).
The detour x_i-b-a-y_i adds 2 to every damaged path, so it never repairs them. A damaged (0,3) pair (x_i, v) is repaired
only through x_i-b-x_j-w-v (v within 2 of another x_j) or x_i-b-a-y_j-v (v adjacent to another y_j); a (1,2) pair
(u, v) only through u-x_i-b-x_j-v (v adjacent to another x_j) or the mirror through a. Best known: 144 bad pairs
(guided SA, handsoff c24/b686_144.edges, copy it from git branch claude/bipartite-d6-d5-search-80gtg5 if you want).
Task: write a fast evaluator (BFS from the vertices near the insertion is enough for the change, or full score65), then
search STRUCTURED choices of the 5 edges: (i) x_1..x_5 all adjacent to one B-vertex w; (ii) deleted edges alternating with
kept edges on a 10-cycle (x_i ~ y_(i+1)); (iii) greedy: each next edge chosen to maximise repaired damage of the
previous ones; (iv) a design of your own; (v) k = 3 or 4 deleted edges (a, b of degree k+1). Report the best bad count
and, for it, how many damaged pairs stay unrepaired by kind. Beat 144 if you can; explaining why not is also a result.

## h2: two hub orbits per side, type "1,6,6|1,6,6" (Haar degree 4), n = 8m/3
mcos (shared/mcos.c) supports it: TYPE="1,6,6|1,6,6" N="4,1,1,1,0,0,1,0,0" (blocks row-major over A-orbits x B-orbits:
A0 has 4 Haar neighbours and one hub in each B hub orbit; each hub is joined to one coset of 6 regular vertices).
m = 258 (688 vertices), 264 (704), 270 (720); only groups with elements of order 6. Calibrate first: mcos TYPE="1|1" on
SmallGroup(342,12) with SEED=4 reaches cost 0 in about 20 s. Screen every nonabelian group of these orders
(SECS=15 per class combination, MAXCOMB=6, one seed), then deep runs on the best 3 groups (SECS=100, 4+ seeds, EDGES= to
write the best graph; score it with score65). Report the best mcos cost per order and the best bad count.

## h3: two regular orbits + C3 hubs, type "1,1,3|1,1,3", n = 14m/3
Restricted to its index-2 subgroup SmallGroup(147,5), the best 686-vertex hub graph (shared/cost2_294_11.edges, bad
294, proven optimal in its own family) lies in this family, so the family on SmallGroup(147,5) contains a cost-2-like
point and has more freedom. mcos: TYPE="1,1,3|1,1,3" N="a,5-a,1,5-a,a,1,1,1,0" for a = 3, 4, 5 (blocks row-major
A0'B0', A0'B0'', A0'B1, A0''B0', A0''B0'', A0''B1, A1B0', A1B0'', A1B1). Opus measured mcos at cost 26-30 after 20 s
with a = 4 on 147_5, so annealing alone is weak here. Task: (1) screen all groups of order 147 (n = 686) and 150
(n = 700) with mcos, a = 3, 4, 5; (2) write a tabu search for this type (start from shared/t18.c, which is the same idea
for "1,k|1,k": full-neighbourhood steps over single element/coset changes; generalise its blocks to the 9 blocks above)
and run it on the best groups with several seeds. Report the best cost per group and the best bad count.

## h4: tabu with the algebraic cost, hub families k = 2 and k = 4
tools/hubk.c evaluates the family "Haar degree 5 + hubs of size k + hub graph of degree 6-k" by six covering conditions
(cond_side/all_conditions; validated against BFS; total missing 0 <=> diameter 5) and searches it exactly. Exact search
is too large for k = 2 (n = 3m: m = 230, 232, 234 give 690, 696, 702) and for k = 4 at m = 280 (n = 700, 40 groups).
Task: write hubtabu.c: copy hubk.c, keep the cost (all_conditions, sum of the six misses) and replace the exact search
by a tabu search over (S, K, H, R): moves change one element of S (any group element), K or H to another subgroup of order
k, or swap one double coset of R for another of the same size (R must stay a union of H-K double cosets with
|R| = k(6-k)). Keep a tabu list, aspiration, perturb after a stall. Run k = 2 on all nonabelian groups of orders 230, 232,
234 and k = 4 on orders 276 and 280 (short screens, then deep runs on the best). On cost 0: write the edge list with
hubk's build() and run score65 and apsp. Report the best cost per (k, order).
