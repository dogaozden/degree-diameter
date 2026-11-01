# deep-65: an Opus-led deep run on the (6,5) cell (Nov 1, 2026, 01:30-05:35 UTC)

Target: a bipartite graph with maximum degree 6 and diameter 5 on more than 684 vertices (table value 684, the Haar
graph of C6 x (C19:C3) = SmallGroup(342,12)). Brief: depth on the two leads the hands-off squad (handsoff-65) left at
local minima: (a) the 684 graph plus one vertex pair (686, bad 144) and (b) the Haar + hub family "1,6|1,6" on
SmallGroup(294,11) (686, mcos cost 2, exact search estimated at 1e12 evaluations).

## Result

**No record.** `records/` holds nothing. What changed is that both leads are now understood, and the main one is closed
exactly:

- **Lead (b) is closed at 686.** The "1,6|1,6" hub family is exactly six covering conditions on (S, KA, HB) in the group.
  After the right symmetry reduction, a group of order 294 is about 6.5e8 subsets, searched in 76 s, not 1e12.
  No member of the family on any of the 23 groups of order 294 has diameter 5. The cost-2 graph on SmallGroup(294,11)
  is the global optimum of its family, not a local minimum. The same holds at 700-728 vertices (all 111 non-abelian
  groups of orders 300, 306, 312 that have a subgroup of order 6: no solution, best 21).
- **Why the minimum is 2:** in all optimal subsets the two missing elements are an inverse pair inside the abelian
  normal subgroup C7 x C7. Every other coset of C7 x C7 is fully covered. The deficit sits in the zero-weight
  (closed-walk) words, where commutativity makes walks collide.
- **Lead (a) cannot be repaired locally.** Deleting any edge of the 684 graph damages only same-side pairs at distance 4,
  and each damaged pair has an endpoint at the edge or next to it. The x-b-a-y detour adds 2 and repairs none of them.
  A Haiku card built designed insertions on this analysis and found that 117 of the 294 damaged pairs cannot be
  repaired by any choice it tried. Its best is 144, tying the hands-off value with a different design.
- **Generalisations searched exactly:** "Haar degree 5 + hubs of size k + hub graph of degree 6-k" (k = 6 is lead b).
  k = 3 on SmallGroup(258,2) (688): closed, best 4. k = 3 on 258_1: closed. k = 4 on SmallGroup(280,35) and (280,34)
  (700): closed. k = 3 on C11 x SL(2,3) and C11 x S4 (704): closed (best 4 and 6).
  Haiku tabu screens over k = 2, 3, 4 at 690-720 vertices found nothing below cost 3-4.

## Lead (b): the hub family, exactly

Model (NOTES.md has the derivation): G of order m, S a 5-subset, KA and HB subgroups of order 6. A0 = B0 = G with
x ~ xs; each left coset xKA of A0 gets a hub (B1) and each left coset yHB of B0 gets a hub (A1). The graph is 6-regular
on 2m + 2m/6 vertices (686 at m = 294). The parameters (S, g1, g2, H, K) of t18/mcos only enter through
KA = g1 K g1^-1 and HB = g2^-1 H g2. c28 multiplied in 49^2 choices of (g1, g2) on top of (H, K), but those only
conjugate the subgroups.

Diameter <= 5 iff every same-side pair is at distance <= 4. Reading off the walks gives six covering conditions
(T = SS^-1, T' = S^-1 S):
(1) {e} u T u KA u TT u T KA u KA T u S HB S^-1 = G, (2) (T u KA) S HB = G, (3) HB T' HB = G, and their duals (4)-(6).
Symmetry: (S, KA, HB) ~ (d^-1 S c, KA^d, HB^c) and the side swap. So KA and HB are fixed to class
representatives, and S is enumerated with the first element normalised by the N(KA) x N(HB) orbits.
Checks: the c18 cost-2 state rebuilds to bad 294, identical to its edge list. The reduced search and an unreduced
brute force agree on 157 small groups (degree 4). Small solutions rebuild to graphs that apsp.c calls VALID at D = 5.

| groups | n | result |
|---|---|---|
| all 23 groups of order 294 | 686 | no solution; minima 294_11 **2**, 294_12 3 (tabu had 4), 294_7 7 (S3 hubs), others 16+ or nothing passes the hub-level conditions |
| 45 + 8 + 58 non-abelian groups of orders 300, 306, 312 with order-6 subgroups | 700-728 | no solution; best 21 (300_23, 300_24); 521 of 536 class pairs have no subset passing the hub-level conditions |

Near-miss structure (294_11): 12 optimal subsets, 6 per side (duals). In each, three elements of S lie in N = C7 x C7,
the missing pair {f, f^-1} has order 7 and lies in N, and per-coset coverage of condition (1) is 47/49 on N and
49/49 elsewhere. The 684 record has the same shape (a C6 quotient) over a non-abelian core C19:C3. At 686, every
group of order 294 has an abelian Sylow-7 subgroup, so this obstruction is built into the family.

Lift view: nauty gives Aut(cost-2 graph) of order exactly 294. Its C7 x C7 acts freely, so the graph is a regular lift
of a 14-vertex base (tools/hub2lift.py, tools/graph2lift.py). In that much larger family (29 free voltages), no lift
within 2 voltage changes has diameter 5 (900,792 checked). Tabu from random voltages reaches only cost 76, against
the structured 12. Breaking the symmetry makes the search harder without opening a way down.

A second bad-294 graph (round 1, h3): type "1,1,3|1,1,3" (two regular orbits + C3 hubs) on SmallGroup(147,3) =
C7 x (C7:C3), automorphism group of order exactly 147, not isomorphic to the 294_11 graph. It is also a C7 x C7 lift
(no diameter-5 lift within 2 voltage changes, 922,029 checked) and a strict 2-change minimum in its own parameter
space (round 2, h5: 1.92M pairs, 132 tied at 294, next best 1323).

## Generalisation: hubs of size k (tools/hubk.c)

Family: Haar part of degree 5, hubs of size k (cosets of K and H, |K| = |H| = k), and a hub-hub relation R (a union of
H-K double cosets, |R| = k(6-k)), n = 2m + 2m/k. The six conditions carry over with R in place of the hub-hub walks.
They are validated against BFS from the four orbit representatives on random parameters for k = 2..6
(0 mismatches). k = 5 (a perfect matching between hub orbits) and k = 4, 2 use double cosets that mcos/t18 cannot.

| k | group | n | exact result |
|---|---|---|---|
| 3 (one full double coset; hub3.c) | SmallGroup(258,2) = C2 x (C43:C3) | 688 | no solution, 1.5e10 configurations, best 4 (= c22's tabu) |
| 3 | SmallGroup(258,1) = C43:C6 | 688 | no solution (nothing passes the hub-level conditions) |
| 4 | SmallGroup(280,35) = C2 x (C5:(C7:C4)) | 700 | no solution (round-1 tabu: cost 3 on a state failing condition (5)) |
| 4 | SmallGroup(280,34) = C14 x (C5:C4) | 700 | no solution |
| 3 | SmallGroup(264,12) = C11 x SL(2,3) | 704 | no solution, 8.76e10 leaves (71 R-orbits), best 4 (= round-2 tabu) |
| 3 | SmallGroup(264,31) = C11 x S4 | 704 | no solution, 8.76e10 leaves, best 6 (tabu had 4 on a state failing a hub-level condition) |

Not finished, not claimed: k = 3 on 258_3/4/5 and k = 5 on 290_1-3 (the hub subgroup is normal; R then has
10^4-10^5 choices), k = 4 on order 276 (tabu best 68, so far), and k = 2 at all orders (about 1e11 leaves per group,
because the hub-level conditions do not filter when hubs have size 2). Haiku tabu screens (round1/h4, round2/h6;
cost = total missing elements): k = 2: 240_112 cost 4 (n = 720), 238_1 6 (714), 234_1 7 (702), 230_1 10 (690);
k = 3: 270 best 6 (720); k = 4: 288_893 13 (720, 88 of 1045 groups sampled), 276 best 68, 284 best 300.

## Lead (a): the 684 graph plus a vertex pair

Damage of one deleted edge (shared/damage684.c): 44, 47, 49, 60, 81, 83 pairs for the six edge types. All of them are
same-side pairs at distance 4 whose only 4-path used the edge, in two kinds: (0,3) = an endpoint of the edge and a
vertex at distance 3 from the other endpoint (23-42 per edge), and (1,2) = a neighbour of one endpoint and a vertex at
distance 2 from the other (18-39). No opposite-side pair is ever damaged.
For an insertion a ~ b, a ~ y_i, b ~ x_i, the detour x_i-b-a-y_i adds 2 and never helps. A damaged pair is repaired
only if its far endpoint is adjacent to, or within 2 of, the endpoints of the OTHER deleted edges. That is a few
dozen vertices, against 40-80 partners per deleted edge.
Round 1, h1 tested designs built on this: star, alternating 10-cycle, beam, greedy, and k = 3-6 deletions.
Best 144: 6 deletions, no a-b edge, a and b both of degree 6; a 1- and 2-exchange local optimum, reached by 5 seeds.
In it, 294 pairs are damaged, 177 repaired, 117 unrepaired (54 (0,3), 63 (1,2)), plus 27 new far pairs at a and b.
Structured designs: 154-234. This lead has no path to 0. Surgery would have to remove the damage, and every edge of the
684 graph carries 44+ pairs that only nearby vertices can reroute.

## Squad rounds (haiku-squad skill; LOG.md)

Round 1 (02:38-03:20, 4 cards): h1 surgery by design (144, see above); h2 "1,6,6|1,6,6" (far, bad 1634+); h3
"1,1,3|1,1,3" on 147/150 (bad 294 on 147_3, new non-isomorphic near miss); h4 tabu with hubk's algebraic cost (k = 4
cost 3 at 700; k = 2 cost 7 at 702).
Round 2 (03:22-04:05, 3 cards): h5 deepened the 147_3 near miss (strict 2-change minimum, other seeds and groups worse);
h6 hubtabu sweeps (k = 2 cost 4 at 720 on 240_112; k = 3 cost 4 at 704 on C11 x SL(2,3) and C11 x S4, sent to exact
search); h7 lifts of the 14-vertex hub bases by the five groups of order 50. No group, abelian or not, came near the
structured 12. The non-abelian D50 and (C5 x C5):C2 were worse, but random-start tabu cannot even re-find 12 over
C7 x C7, so this does not test the non-abelian-core reading either way.

## Spend (tools/session_usage.py --arm deep-65, 01:30:05-05:30 UTC; the wrap-up adds a little Opus)

| model | messages | output tokens | units | share |
|---|---|---|---|---|
| Opus (me) | 140 | 284,113 | 1.252 | 98% |
| Haiku (7 runs) | 269 | 386,942 | 0.028 | 2% |

Opus cache reads were 43.5M tokens (140 turns over a long context); that and about 284k output tokens of derivation and code are the cost. The exact searches themselves used about 9 CPU-hours on the 4-core container and no model time.

## Comparison with handsoff-65 (same cell, the day before)

| | handsoff-65 | deep-65 |
|---|---|---|
| structure | Opus plans and checks; 28 Haiku runs search | Opus derives and searches; 7 Haiku runs on Opus cards |
| wall clock | 5.5 h | 4.1 h |
| spend (units) | Opus 0.542 + Haiku 0.280 = 0.822 (34% Haiku) | Opus 1.252 + Haiku 0.028 = 1.279 (2% Haiku) |
| record | none | none |
| families covered | about 20, broadly, by annealing/tabu | 1,6|1,6 closed exactly at 686 and 700-728; k-hub family exact on 258, 280, 264; 5 new families screened by Haikus |
| lead (b) | cost 2 found; "exact search ~1e12, out of reach" | cost 2 proven optimal on every group of order 294 in about 10 CPU-minutes; the obstruction located (abelian core) |
| lead (a) | 144, "strict local minimum" | why: damage is local and unrepairable through two new vertices; 117 pairs left in the best design |

Plain verdict. On the record, the same: none. On understanding, this run did better. The hands-off run's two open
leads are now closed or explained, and the main family is settled by an exhaustive search (checked against brute force on small cases) instead of
a 1e12 estimate. On breadth it did worse: 7 Haiku runs against 28. It also cost more: Opus spent about twice the hands-off
coordinator's total, because the work was derivation, code and verification in a long context. A cheaper version would
do the derivation in one Opus session and hand the sweeps to Haiku cards much earlier. Most of the exact searches were
plain compute that needed no model at all.
The Haikus did well on cards with a ready tool and a precise question (h4, h6 sweeps; h5 exact 2-change check; h1
designed insertions with the damage facts given). Their best finds (h3's second near miss, h6's cost-4 points at
704/720) were all checked or sent to exact search by me. None was a record.

## Files

- tools/hubeval.c (one state: six conditions + edge list), tools/hubex.c (exact 1,6|1,6, NORED=1 brute-force check),
  tools/hub3.c (exact 1,3|1,3 full double cosets), tools/hubk.c (general k: rand = BFS validation, ex = exact),
  tools/hub2lift.py and tools/graph2lift.py (graphs as voltage lifts), tools/gap_tables.g.
- runs/ (the output of every exact search: one file per group, near states of 294_11), NOTES.md (derivations and run
  log), round1/ and round2/ (cards, scoreboards, Haiku code and notes),
  shared/ (scorer, apsp.c, lift tools, the two bad-294 lifts).
- Reproduce the main result: `gap -q -c 'ORDER:=294; OUTDIR:="groups";' tools/gap_tables.g` then
  `gcc -O3 -march=native -o hubex tools/hubex.c && for i in $(seq 1 23); do ./hubex groups/sg_294_$i.txt 6; done`.
