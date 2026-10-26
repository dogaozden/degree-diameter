# own-small round 1 cards (16). Shared rules, tools and the "already found / ruled out" list: r1/HEADER.md.

T = /home/user/degree-diameter/research/squads/own-small/tools, SEEDS = /home/user/degree-diameter/research/squads/own-small/seeds.
Each card works in /home/user/degree-diameter/research/squads/own-small/r1/<card>/ and scores with `$T/bin/score48 EDGES d D`.

## (3,10): more than 800 vertices, diameter <= 10

**a1: symmetry-breaking repair of the n = 880 near miss.** The seed is the 2+2 lift of SmallGroup(220,2) = C4 x (C11:C5)
with cost 2 (220 far pairs). $SEEDS/g220_2_cost2.volts lists all 124 cost-2 assignments up to Aut ("2 : 0 a 0 0 b c" =
flift eval voltages of $T/bases/cubic/b22_cubic.txt edges in file order, flift convention (u,x)~(v,g*x)). Group table:
$SEEDS/groups/g220_2.txt (gap_export text format, id 2) and /tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/groups/b220/g220_0002.bin is NOT
guaranteed to exist, so build your own .bin from the text table. salift/salift2/requot use the right-multiplication
convention (u,g)~(v,g*a): use the INVERSE voltages there. Plan: re-express a few cost-2 lifts over subgroups H of index
2, 4, 5 (then 10, 11) with requot.py, giving a (2[G:H])+(2[G:H]) base over H, and anneal from there (salift2 with D=10
if its header allows, otherwise flift with the requot base: voltages free, base fixed, low T0 so it stays near the seed;
many restarts). The 2+2 family over this group is proved minimal at cost 2, so only symmetry-breaking can help.
The (3,7) job tried the same on its near misses with no move below the start: vary temperatures and moves. Score: n = 880.

**a2: the n = 816 near miss and all groups of order 136.** Seed: 3+3 lift of meta:17:8:4 (Z17 x| Z8, order 136), cost 2
($SEEDS/nm816_meta17_8_4.out: flift .sol, base $SEEDS/base33_0.txt; edges $SEEDS/nm816_meta17_8_4.edges). (1) Exhaustive
3+3 lifts (all 3 connected cubic 3+3 bases, see $T/enum_bases.py) over EVERY group of order 136 (GAP: 15 groups),
Aut-reduced (first free voltage over Aut(G)-orbit reps, see $T/gap_export_aut.g), with flift eval and LIMIT=0/ONLYLOW.
(2) Requot repair of the seed over subgroups of index 2 and 4 (6+6 / 12+12 bases), annealed as in a1. Score: n = 816.

**a3: delete-and-rematch surgery.** From a near miss (880: $SEEDS/nm880_g220_2.edges; 816: $SEEDS/nm816_meta17_8_4.edges),
delete k vertices on each side (k up to (n - 802)/2), then re-match the 3k-ish deficient vertices on each side by a new
bipartite matching (multi-edges forbidden) so the graph is cubic again; choose the deleted set and the matching to
minimise far pairs (start by deleting vertices on far pairs, or a whole fibre slice; anneal over (deleted set,
matching)). This is a bigger move than the 2-switches that already failed. Score with score48 3 10 (n >= 802).

**b1: covers of the Tutte 12-cage (GH(2) incidence graph, 126 vertices, girth 12, diameter 6).** Base:
$T/bases/cubic/gh2.txt. Covers over Z7 (n = 882) and the 5 groups of order 8 (n = 1,008). flift only takes bases <= 64
vertices, so write your own annealer: with |G| <= 8 each fibre's reached set is one byte; BFS from the 126 roots (u,e)
(the group acts semiregularly), right-multiplication by a voltage is a 256-entry byte table; move = change one cotree
voltage; cost = (root, lift vertex) pairs at distance > 10. Then try voltage assignments invariant under a subgroup of
Aut(base) (order 12,096) to shrink the search. Score: n = 882 / 1,008.

**b2: covers of small edge-transitive bases (<= 64 vertices) over ALL groups of the right order.** Bases: bipartite
cubic arc-transitive / semisymmetric graphs with <= 64 vertices and small diameter from the Foster census (Heawood 14,
Moebius-Kantor 16, Pappus 18, Desargues 20, F24, F26, Tutte 8-cage 30, F32, F38, F40, F42, F48, F50, CSS54, F56, F64;
take bipartite ones; $T/bases/cubic has five of them). For base size b, group orders N with 802 <= bN <= 1,000; ALL groups
of that order from GAP (non-abelian first; skip orders with > 60 groups or sample them). Earlier only metacyclic and
dihedral groups with 20-45 s anneals were tried (best Moebius-Kantor x Z51, cost 46). Screen with short flift anneals
(3-5 s), push the best 3 pairs with 300 s. Score: the lift's n.

**b3: covers of mid-size edge-transitive bases (65..170 vertices) over small groups.** Bases from the Foster census
(sparse6 zip in HEADER): bipartite cubic graphs with 65..170 vertices and diameter <= 7, e.g. F80, F96, F98, F102,
CSS110, F112, CSS120, F128, F144, F150, F162 and F168 = the (3,7) record graph (diameter 7; over Z5 n = 840, over Z6/S3
n = 1,008). Group orders 5..12 with 802 <= bN <= 1,010. Write your own annealer (flift is limited to 64 base vertices; b1
writes one for the 126-vertex cage, do not wait for it). Score: the lift's n.

**c1: 3+3 bases over ALL non-abelian groups of order 134..170 except 136** (n = 804..1,020). GAP export + Aut reps;
screen each (group, base) with short flift anneals (3 s), then exhaustive flift eval (first free voltage over Aut-orbit
reps, the rest all) on the best 3-5 groups. Earlier: only 17 metacyclic/abc groups with 8 s anneals; the best 3+3 is
Z17 x| Z8 at order 136 (cost 2, card a2 has it). Score: n = 6N.

**c2: 4+4 bases over ALL non-abelian groups of order 101..125** (n = 808..1,000). The 6 connected cubic 4+4 bases
($T/enum_bases.py 4 DIR). Screen with short flift anneals, push the best with 300 s runs and several seeds. Earlier: only
metacyclic groups of order 101..130 with 8 s anneals (best 12). Score: n = 8N.

**c3: 5+5 and 6+6 bases with joint base+voltage annealing (salift, D=10) over groups of order 68..100** (n = 810..1,000
with 5+5: N = 81..100; 6+6: N = 68..83). salift reads gap_export text tables (export the orders you use with
$T/gap_export.g into your folder). In the (3,7) job salift found the record from scratch with bases up to 6+6; it has never
been run at D = 10. Screen many groups (20 s each), push the best (300 s, several seeds). Score: n = 2pN.

**w1: wildcard (3,10).** Find an approach that none of the other cards (a1-a3, b1-b3, c1-c3, w2) and none of the ruled-out
list in HEADER uses. Ideas nobody has taken (use or ignore): permutation-voltage (non-regular) covers with a structured
permutation group; graphs with a semiregular group that swaps the two colour classes; a construction from a (3,10) graph
of the general (non-bipartite) table; "fibre splicing" of two different near misses. Write the idea in one line first,
then code it and score it.

**w2: wildcard (3,10), theory first.** Before searching, work out WHY the 2+2 lifts at orders 201..230 stop at cost 2
(one orbit of far pairs at distance 11) and which group property the two best groups (SmallGroup(220,2) = C4 x (C11:C5),
and Z17 x| Z8 for 3+3) share; turn that into a fast group-level filter (e.g. count distinct elements reached by reduced
words of length <= 10 in the voltages), check it ranks the known near misses high, then apply it to choose groups and
bases nobody has searched (any base size, n in 802..1,000) and search the top ones. Score with score48 3 10.

## (3,9): more than 506 vertices, diameter <= 9

**e1: 3+3 and 4+4 bases over ALL non-abelian groups of order 85..110 (3+3, n = 510..660) and 64..80 (4+4, n = 512..640).**
Screen with short flift anneals (D = 9), push the best, exhaustive (Aut-reduced flift eval) on the best 2-3 3+3 groups.
Score: score48 EDGES 3 9.

**e2: covers of edge-transitive bases at (3,9).** Tutte 12-cage x Z5 (n = 630; own annealer as in b1, base
$T/bases/cubic/gh2.txt); bases <= 64 vertices from the Foster census with diameter <= 5 over ALL groups with
508 <= bN <= 640 (Heawood x Z37 was cost 88 with metacyclic groups only); salift (D=9) 5+5/6+6 over groups of order
43..64. Score: score48 EDGES 3 9.

## (3,7): more than 168 vertices, diameter <= 7

**h1: delete-and-rematch from the n = 180 near misses down to 170..178.** The best (3,7) near misses (cost 4 = 36 unordered
far pairs) are on branch claude/bipartite-d3-d7-search-9kfg4g: `git show origin/claude/bipartite-d3-d7-search-9kfg4g:research/d3D7/seeds/nm180_c3xs3_b5_14.edges`
(and nm180_c30_b31.edges, nm192_haar96_65.edges; `git fetch origin claude/bipartite-d3-d7-search-9kfg4g` first). Delete
k = 1..5 vertices per side, re-match the deficient vertices by a new bipartite matching so the graph is cubic again,
choose deletions and matching to remove far pairs (exhaustive for small k over deletions touching far pairs, annealing
for larger k). Note from that job: for even n >= 170 a (3,7) graph must be cubic. Score: score48 EDGES 3 7.

## (4,8): more than 2,184 vertices, diameter <= 8

**f1: quartic 2+2 and 3+3 lifts over ALL groups of order 547..565 (2+2, n = 2,188..2,260) and 365..376 (3+3, n =
2,190..2,256).** Bases $T/bases/b22_t1.txt, b22_t2.txt and the 3+3 quartic bases (write them: 3x3 matrices with row
and column sums 4). GAP export, non-abelian groups first, small abelianization first (an abelian quotient that is too
large is fatal). Screen with flift anneals, push the best. Earlier: 2+2/3+3 lifts only over metacyclic groups at (4,9).
Score: score48 EDGES 4 8.

## (4,9) and (4,8) wildcard

**w3: wildcard for (4,9) (or (4,8)).** Five rounds of an earlier squad tried the families in HEADER's ruled-out list.
Find an approach none of them used (a new group family of order 2,486..2,600 with small abelianization and no central
involution, a non-Haar construction, a different base, or a construction from a known graph), write it in one line, code
it and score it with score48 EDGES 4 9 (or 4 8).
