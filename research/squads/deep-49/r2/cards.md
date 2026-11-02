# deep-49 round 2 cards (rolling: each starts when a round-1 card hands back)

Common part: as in research/squads/deep-49/r1/cards.md ("Common part"), except: work in research/squads/deep-49/r2/<card>/
and append scoreboard lines to research/squads/deep-49/r2/scoreboard.jsonl. Append ONE line per group or family (the best
value), not one line per sub-run.

## r2a: non-direct non-solvable groups of order 2,520, and the SL(2,5) x F21 near miss

Round 1 (card c1, r1/c1/) found exact Haar minima at order 2,520: SL(2,5) x (C7:C3) = 4 (a new near miss at n = 5,040),
A7 6, A6 x C7 8, S5 x F21 8, PSL(2,7) x C15 > 8. The direct products are covered by c1. Do two things.
(1) Groups that are not direct products: the fibred products S5 x_C2 X = {(s, x) : sign(s) = chi(x)} for X of order 42
with a homomorphism chi onto C2: X = D21 (DihedralGroup(42)), X = C7:C6 (SmallGroup(42,1)), X = C3 x D7
(DirectProduct(CyclicGroup(3), DihedralGroup(14))). Build each in GAP as a subgroup of DirectProduct(SymmetricGroup(5), X)
(check Size = 2520 and that it is not isomorphic to S5 x F21: compare AbelianInvariants and the number of conjugacy
classes), export it, run hx LIMIT 0 (chunks), then the exact minimum (LIMIT 2, 4, 6, 8). Also any other non-solvable group
of order 2,520 that you can build and that is not already in r1/c1 (look at r1/c1/NOTES.md first).
(2) The near miss: take r1/c1/g/SL25x_C7C3.tab/.aut (and its hits files) and describe the cost-4 sets like card c4 did
for the metacyclic walls (r1/c4/NOTES.md, r1/c4/hx.c has a "must cover" option): how many sets, which elements are missed
(order, conjugacy class, side), whether the central involution of SL(2,5) is ever missed. Then: exact minimum when the
most frequently missed class is required to be covered. Score = the exact minima.

## r2b: two more hub types, screened across groups (one-sided stabilisers; cubic Haar + hub orbits)

Tools (read the comment at the top of each): tools/mixed.c and tools/hubs.c (build: gcc -O3 -march=native -o X X.c).
- `mixed TABLE CPUSECONDS SEED 9 OUT.edges`: A = G regular, B = two G-orbits with point stabilisers {e,h1}, {e,h2}
  (h_i non-central involutions), n = 2|G|. Needs groups with many non-central involutions.
- `hubs TABLE CPUSECONDS SEED 9 OUT.edges`: cubic Haar graph of G plus one hub orbit per side (stabilisers of order 4),
  n = 2.5|G|, so |G| in 1,989..2,100 and divisible by 4 gives n in 4,972..5,250.
Both are random-restart screens; cost = sum over the BFS roots of the vertices on the root's side not within 8 (0 iff
diameter <= 9). Director's calibration (20-30 CPU s): mixed on Z_125 x|_7 Z_20 gives 17 (its best Haar set has cost
>= 13), on A7 21 (Haar 6); hubs on Z_101 x|_5 Z_20 gives 28. CPU seconds run at about half wall speed on this loaded
machine, so use CPUSECONDS <= 45 with `timeout 100`.
Do: (1) mixed on every group of order 2,486..2,600 that you can build with at least 10 non-central involutions: the
tables in r1/c1/g/ (non-solvable, order 2,520 and 2,640), split metacyclic Z_m x|_r Z_k with r^(k/2) != 1 (build with
tools/mkmeta.py; list them with a small script, at most ~40, prefer large order of r), and GAP SmallGroup tables for
orders where SmallGroupsAvailable (use tools/export_group.g + build_tab.py). (2) hubs on groups of order 1,992..2,100
divisible by 4 with |G/G'| <= 309 (GAP SmallGroups has most orders <= 2,000 and some above; also metacyclic via mkmeta
and non-solvable ones like PSL(2,8) x C4, PSL(2,7) x A4, SL(2,5) x C17, A5 x C34). 1 screen per group, then 3 more seeds
on the best 5 groups of each family. Verify any best file with tools/score48 (far pairs) and report the best per family.
Score = best cost per group (one scoreboard line per group).

## r2c: the luck curve just below the record (orders 2,440..2,485)

Every group of order 2,486..2,600 checked so far has no Haar set of cost 0 (exact, hx). How dense are cost-0 groups just
below? For every split metacyclic group Z_m x|_r Z_k with m k in 2,440..2,485, multiplicative order d of r mod m >= 8
and |G/G'| = k * gcd(r-1, m) <= 309 (deduplicate r ~ r^t, gcd(t,k) = 1; list them first with a script, sorted by order
descending), run `tools/mkmeta.py m k r prefix` and hx LIMIT 0 (chunks under 100 s). Record for each group: N, m, k, r, d,
and 0 (a cost-0 set exists: give it) or ">0". Also add the SmallGroups-library groups of these orders (GAP
SmallGroupsAvailable; export with tools/export_group.g) with |G/G'| <= 309 that are not metacyclic. Goal: the list of
orders <= 2,485 that have a diameter-9 Haar graph. Score = 0 or ">0" per group (one scoreboard line per group).

## r2d: auditor (independent re-checks of the exact claims)

The round-1 certificates all rest on tools/hx.c (exact Haar search with an Aut(G) reduction written by the director).
Check them independently:
(1) Read hx.c and look for any way it could skip a set S = {e, x, y, z} (orbit representatives of x under Aut(G),
y over Stab(x)-orbit representatives, z over all elements with orbit index >= that of y; Schreier generators for the
stabiliser). Write down any doubt precisely.
(2) Independent code: the handsoff-49 exhaustive searcher exh3.c (git show
origin/claude/handsoff-49-bipartite-search-hy5axz:research/squads/handsoff-49/w11/exh3.c > exh3.c; it reduces only by
inner automorphisms, "tab FILE" mode reads the same table format as hx) or your own brute force. Re-run, with it:
(a) the record group (tools/mkmeta.py 71 35 49): cost 0 must exist; (b) Z_101 x|_5 Z_25: minimum 2;
(c) SL(2,5) x (C7:C3) (r1/c1/g/SL25x_C7C3.tab): minimum 4 claimed (so: no set of cost <= 3, and one of cost 4);
(d) three groups certified ">0" by hx, chosen at random from r1/c2 and results/smallgroups_*_hx.log (tables: rebuild with
mkmeta.py or with GAP from the .exp/.g files); (e) c4's constrained minimum 8 for Z_104 x|_7 Z_24 with the central
involution 52 covered on both sides (r1/c4/hx.c HX_MUST option; check one witness set of cost 8 in python and that no
cost <= 7 set exists, with your own code if feasible). Report agreement or any disagreement. Score = number of claims
re-checked and number confirmed.

## r2e: extend the metacyclic certificate to orders 2,531..2,600

Same job as round-1 card c2 (read r1/c2/NOTES.md and reuse r1/c2/driver.py and mkcand.py), for the orders in
2,531..2,600 that GAP's SmallGroups library does NOT have (check with SmallGroupsAvailable; the available ones are already
done in results/smallgroups_2531_2600_hx.log). Split metacyclic Z_m x|_r Z_k, deduplicated, |G/G'| <= 309, order d of r
>= 3, sorted by d descending; hx LIMIT 0 in chunks. Score per group: ">0" or 0 (give the set). One line per group.
