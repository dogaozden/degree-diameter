# deep-49 round 1 cards (written by the Opus director, 2026-11-01 ~23:15Z)

## Common part (sent to every card)

Goal of the squad: a bipartite graph with maximum degree 4 and diameter 9 on 4,971 or more vertices (the table value is
4,970: the Haar graph of the metacyclic group Z_71 x|_49 Z_35, research/squads/deep-49/seeds/valid4970.edges). Your card
is one narrow piece of that; an exact negative answer is a useful result.

Haar graph H(G,S): vertices (g,A), (g,B); edges (g,A) ~ (g s, B), s in S, |S| = 4. Diameter <= 9 iff
(S S^-1)^4 = G and (S^-1 S)^4 = G. cost = number of group elements missed on the two sides (0 iff diameter <= 9).

Repository root: /home/user/degree-diameter. Tools (read and copy them, do not edit): research/squads/deep-49/tools/
(README.md there). The main ones:
- `hx TABLE AUT LIMIT 9 XFROM XTO HITFILE`: exact Haar search reduced by Aut(G). `MIN >0` means: no Haar set of cost 0
  exists (exhaustive). stderr line 1 gives the number of x representatives; split long runs with XFROM XTO.
- GAP 4.12 is installed. Run `gap -q --quitonbreak FILE.g < /dev/null`. `Read("/home/user/degree-diameter/research/squads/deep-49/tools/export_group.g");`
  then `ExportGroup(G, "file.exp");`, then `python3 tools/build_tab.py file.exp prefix` writes prefix.tab and prefix.aut.
- `mkmeta.py m k r prefix` for split metacyclic groups. `haar_edges.py TABLE OUT 0 x y z` writes the edge list.
- `apsp EDGES 4 9` is the independent check (RESULT VALID / INVALID); `score48 EDGES 4 9` counts far pairs.

Rules:
- Work only in your folder research/squads/deep-49/r1/<card>/ (create files there). No git commands.
- The machine has 4 cores shared by 9 agents: single-threaded, prefix heavy commands with `nice -n 10`, at most 1.5 GB.
- EVERY command must finish in under 110 seconds: wrap with `timeout 100`. Split long work into chunks and run the chunks
  one after another (hx: XFROM XTO ranges). Never start background jobs, never wait idle.
- Time box: about 75 minutes of work, then stop and reply.
- Scoreboard: for every finished result append one JSON line to research/squads/deep-49/r1/scoreboard.jsonl, using
  python (json.dumps) to avoid quoting mistakes: {"card": "c1", "idea": "<one line>", "code": "<path>",
  "command": "<exact>", "n": <vertices>, "score": <cost or far pairs>, "exact": true|false, "valid": true|false,
  "next": "<one line>"}.
- If you find cost 0 / far pairs 0 at n >= 4,971: write the edge list into your folder, run `tools/apsp FILE 4 9`
  (must say RESULT VALID) and `tools/apsp FILE 4 8` (must say INVALID), and put that first in your reply.
- Keep a short NOTES.md in your folder (what you ran, results, how to rerun). Final reply: at most 5 lines.

## c1: non-solvable groups of order 2,520 (and 2,580, 2,640), exact

The only non-solvable groups with order in 2,486..2,530 have order 2,520. Earlier exact minima: A_7 6, S_5 x F_21 8,
PSL(2,8) x C_5 8. Build each with GAP (DirectProduct, AlternatingGroup, SymmetricGroup, PSL(2,q), SL(2,q),
SmallGroup(21,1) = C7:C3, SmallGroup(42,1) = C7:C6, DihedralGroup(42) = D21 of order 42, CyclicGroup(n)), export it,
and run hx with LIMIT 0 over all x representatives (chunks under 100 s). Calibrate first: A_7 with LIMIT 5 must give
`MIN >5` (exact minimum 6). Targets, in this order: A6 x C7; PSL(2,7) x C15; SL(2,5) x (C7:C3); SL(2,5) x C21;
A5 x (C7:C6); A5 x C42; A5 x D21(order 42); A5 x C3 x D7(order 14); A5 x C2 x (C7:C3); S5 x C21; then A5 x C43 (2,580),
PSL(2,11) x C4 and PSL(2,11) x C2 x C2 (2,640). For each group finished with `MIN >0`, find the exact minimum if it is
cheap (rerun with LIMIT 2, 4, 6, 8 and stop at the first `MIN c`). Score = exact minimum (or ">L").

## c2: metacyclic groups of the orders missing from the SmallGroups library, exact

All groups of order 2,486..2,530 that GAP's SmallGroups library has are already done (no Haar set of cost 0). The orders
it does not have: 2488, 2490, 2492, 2496, 2499, 2500, 2502, 2504, 2508, 2511, 2512, 2516, 2520, 2528, 2530. Certify the
split metacyclic groups Z_m x|_r Z_k (m k = N, r^k = 1 mod m) of these orders: deduplicate (r and r^t with gcd(t,k) = 1
give isomorphic groups), keep only |G/G'| = k * gcd(r-1, m) <= 309 and multiplicative order d of r mod m >= 3 (d <= 2 is
impossible: research/squads/deep-49/tools/capacity shows |(SS^-1)^4| <= 1,849 then). Most promising first: sort by d
descending. For each: `python3 tools/mkmeta.py m k r prefix` then hx LIMIT 0 in chunks. Then, if time is left, the
non-split ones: GAP `F := FreeGroup("x","y"); G := F / [x^m, y^k * x^-s, y^-1*x*y*x^-r];` (needs r^k = 1 and
s(r-1) = 0 mod m and m | s * (something); just build it and check Size(G) = m*k), `G := Image(IsomorphismPcGroup(G));`,
ExportGroup. Score per group = 0 found or ">0"; report the count certified.

## c3: the luck curve of Frobenius groups, exact minima

How rare is cost 0 near the record? For every Frobenius group Z_p x| Z_k (p prime, k | p-1, k >= 8, r of order k mod p)
with p*k in 2,200..2,800 (there are a few dozen; list them first), compute the exact minimum cost with
`mkmeta.py p k r prefix` and hx, raising LIMIT 0, 1, 2, 4, 6, 8, 10 until hx prints `MIN c` (each run in chunks under
100 s). Note that the record group 71 35 49 is in the list (minimum 0) and 101 25 5 has minimum 2. Produce a table
N, p, k, r, minimum, number of hits at the minimum. Score = the table (scoreboard line per group).

## c4: why the walls are walls (constrained exact searches)

Exact minima known: Z_104 x|_7 Z_24 (N = 2,496): 4 (the central involution z = (52,0), index 52, is always missed);
Z_208 x|_3 Z_12 (2,496): 4 (central involution (104,0)); Z_101 x|_5 Z_25 (2,525): 2.
Copy tools/hx.c into your folder and add an option "must cover element g on both sides" (reject a set when g is not in
(SS^-1)^4 or not in (S^-1S)^4, before computing the cost). Then:
(i) exact minimum for 104 24 7 with z = 52 required (w13 guessed >= 8);
(ii) the same for 208 12 3 with z = 104;
(iii) for 101 25 5: list ALL sets of cost 2 (hx LIMIT 2 9 1 99999 OUT) and, for each, the missed elements as (a, j)
(a = index mod 101, j = index div 101), and the j-parts of S. Tabulate which fibres j are missed and whether a missed
element is ever in the kernel (j = 0). Score = the exact constrained minima.

## c5: inserting vertices by design into the 4,970 graph

The 4,970 graph X (seeds/valid4970.edges; A = 0..2484, B = 2485..4969; it is H(G,S) with G = Z_71 x|_49 Z_35,
S = {0, 2272, 924, 2216}, edge g ~ 2485 + g*s) is tight: deleting one edge makes about 170-180 pairs far. The hands-off
squad annealed a 2-vertex surgery to 160 far pairs at n = 4,972 (delete 4 edges a_i b_i, add a* ~ b_1..b_4 and
b* ~ a_1..a_4). Your job: designs chosen by structure, each family evaluated exhaustively (score48 far pairs):
D1 "twin": a* gets exactly the 4 neighbours b_1..b_4 of a vertex v (by symmetry v = 0); for each b_i delete the edge to
one of its 3 other neighbours a_i (81 choices); b* ~ a_1..a_4. D2 the mirror (b* twin of a B vertex).
D3 like D1 but a* takes 3 of v's neighbours plus b*, b* takes the 3 freed a_i plus a*.
D4 two twins at once: a* twin of v and b* twin of a B vertex w at distance 3 or 5 from v, with the deleted edges forced
by the twins (enumerate w up to the symmetry fixing v).
D5 your own structured family (for example: the 4 deleted edges form one orbit of a subgroup of Aut(X) of order 4 or 2).
Write a fast evaluator (incremental BFS or bitset BFS; score48 is about 0.1-0.5 s per graph). Report the minimum of each
family and the best graph file.

## c6: other hub types: bi-coset graphs of metacyclic groups with a point stabiliser

The Haar graphs above are the bi-coset graphs with trivial point stabiliser. Read tools/bicos.c: for the Frobenius group
Z_p x| Z_k and stabiliser H = <zeta> of order h (2 or 3), vertices (a, j), a in Z_p, j in Z_{k/h}, edges
(a,j)_A ~ (a + r^j u, j + v)_B for (u,v) in a zeta-invariant 4-set N0. The director ran all non-Haar Frobenius cases with
n = 2pk/h in 4,972..5,600: best 88 far vertices (two roots) at 5,256 (p 73, k 72, h 2) and 5,516; most are much worse.
Extend this to composite m: G = Z_m x|_r Z_k with r^k = 1 mod m, H = <(0, k/h)>, zeta = r^(k/h) mod m (skip zeta = 1:
then H is central and the graph is a Haar graph of G/H), h in {2, 3, 4}, zeta-orbits on Z_m of sizes dividing h, N0 any
zeta-invariant 4-set made of orbits (normalise the first orbit's u to a divisor of m). List every (m, k, r, h) with
n = 2 m k / h in 4,972..5,600 and |G/G'| <= 309 first, then search each family exhaustively (two-root BFS, then full
check with score48 for the best). Score = best far count per family.

## c7: non-metacyclic solvable groups of the missing orders

For the orders without SmallGroups data (2488, 2492, 2496, 2499, 2500, 2502, 2504, 2508, 2511, 2512, 2516, 2520, 2528),
find non-metacyclic solvable groups with |G/G'| <= 309 and at most 3 generators, build them in GAP (direct and
semidirect products of small groups, e.g. (C2^4 : C3) x (C13 : C4) = 2,496, SL(2,3) x (C13 : C8), groups of order 2,500
of the form P : C4 with P of order 625, (C7^2 : C3) x C17, C29^2 : C3 is already done), and run hx LIMIT 0 on each. Use
GAP to check |G/G'| (AbelianInvariants) before running. A useful filter: G has a normal abelian subgroup A with G/A of
small order d; then |(SS^-1)^4| is small (for metacyclic groups: d = 1: 309, d = 2: 1,849, d = 3: 4,429), so prefer groups
with a large non-abelian twist. Score = per group 0 or ">0".

## c8: wildcard

Find an approach to a (4,9) graph on more than 4,970 vertices that none of the other cards uses. The others: c1 Haar
graphs of non-solvable groups of order 2,520; c2 split/non-split metacyclic Haar graphs of orders 2,488..2,530 not in
SmallGroups; c3 exact minima of Frobenius groups of order 2,200..2,800; c4 constrained searches at the cost-2/4 walls;
c5 vertex insertion into the 4,970 graph by design; c6 bi-coset graphs with point stabilisers of order 2-4;
c7 non-metacyclic solvable groups of the missing orders. Already known not to work (handsoff-49): local 2-switch
annealing on the record, lifts of GQ W(3) and GH H(3), large-base voltage lifts without symmetry, compound graphs,
random-like bi-Cayley graphs. Pick one idea, implement it, score it with score48/apsp, and report.
