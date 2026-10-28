# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26, session thm-gq-d5 (Opus director), goal: D = 5 theory from generalized quadrangles; (13,5) and (15,5) records. Round 1 (gqd5-r1, 19 Haiku cards, effort high)

Cards (score): c1 max partial ovoid W(9) (51); c2 W(11) by group orbits (68); c3 W(11) by C local search (70); c4 non-friendly
freed sets in Q(4,5) satisfying the exact criterion (3, beats the local-duality limit 2); c5 same in W(5) (1; failed to
reach the explicit 2); c6 third-level/hub routing, 3 levels q=3 (10 hubs, all transitions violate the two-level criterion);
c7 typed assembly test q=5 (1,596 valid; reproduced the director's builder independently); c8 relaxed point sets with hub
rules (0); c9 relaxed line sets (failed, 18); c10 hub-graph table (explicit sizes 5..4,100 for delta 2..12); c11 duality of
W(q), q even (verified q=2,4,8; all-H q=4 r=1: 544 valid); c12 AS(q) (pending); c13 GQ(2,4) levels (144, weak); c14 DM lift +
hubs (0); c15 slot formulas per r (r=3: a+b+4c, r=4: 4b+4c); c16 explicit partial ovoids of W(q) (only q+1 uniform); c17 mixed
hubs (impossible by parity); c18 unjoined level pairs, T2(O) (nothing); c19 7 levels q=5: a random 16-point non-friendly
freed set is repaired through third levels after annealing the other matchings (valid, 2,184).
Verified by the director: c4's 3-point set (exact criterion and brute force), c1/c3 sets (partial ovoids).
Kept: c1's 51-point set (used in (13,5) 11,621, apsp VALID), c19's third-level routing, c4's exact-criterion sets, c15's
formulas. Director's own: typed builder + hub annealer gave (13,5) 11,605 then 11,621; q=11 typed gives 20,696 (40 short of
the lab's 20,736). Next: round 2 on relaxed line sets (pairs repaired by hubs at the ovoid point of the partner line),
larger partial ovoids, whole-graph routing with hubs at q=5,7, exact-criterion sets at q=7,9.

### Round 2 (gqd5-r2, 12 Haiku cards, effort high; fewer cards because the work was CPU-bound on 4 cores)

Cards (score): r2c1 relaxed line sets q=9 (66 points, but 30 partner pairs, more than the hub budget allows); r2c2 relaxed
sets q=11 (87); r2c3 two-partner / pencil relaxations (0: two partners at distinct points cannot be repaired by one hub;
pencils of 2 through a point off the ovoid can); r2c4 W(9) partial ovoid by group orbits (50; nobody beats 51); r2c5 typed
7 levels q=5 with c freed points on every H->H arc, whole-graph annealing with hubs (valid up to c=5, 2,248); r2c6 q=7 no
hubs (16 on one arc, 4 on each of four arcs); r2c7 independent test of the relaxed-pair hub rule (q=5, 1,610 valid, and
diameter 6 without the rule); r2c8 exact small maxima (pending at time of writing); r2c9 explicit hub graphs for every
size (delta 8: 7..153); r2c10 explicit partial ovoid of W(q), size 3q-1, all odd q (with proof; used as Lemma 1.3);
r2c11 exact-criterion sets q=7,9 (pending); r2c12 (15,5) wildcard (0; counting shows the relaxations cannot reach it).
Verified by the director: r2c10's family (q=3..13), r2c7's claim (consistent with Prop. 7.2), r2c9's ranges noted as
computer-checked. Kept: r2c10's family (theorem families), r2c5/r2c6's routing evidence (director's wgr.py at q=9),
r2c2/r2c1 relaxed sets (bounded by the hub budget). Director's own in this round: relaxed-pair hub rule implemented at
q=9 -> (13,5) 11,626 then 11,627 (57-line relaxed set, 14 pairs); independent rebuild sol2edges.py identical; an
independent referee pass on the note (general-purpose agent) found no error in the theorems, several gaps fixed.

### Round 3 (gqd5-r3, 4 Haiku cards, effort high; small on purpose: two of the four cores ran the director's annealer)

Goal: larger relaxed sets (each point = one more vertex at (13,5); 111 points of W(11) would beat (15,5)) and an
independent test of the strengthened hub rule. Cards (score): r3c1 relaxed q=9 by orbits of the spread stabiliser (66;
orbit unions give at most 61, SAT says no 67 under two subgroups); r3c2 relaxed q=11 by orbits (87 unchanged; exact
orbit-union bounds under prime-order subgroups, e.g. an involution class caps invariant sets at 106 < 111); r3c3 relaxed
q=9 as a packing of pairs (66, no improvement; component annealing alone reached 55); r3c4 test of Proposition 7.2 with the A-hub condition only
(q=5: 1,610, q=7: 4,086 valid; breaking the rule for one line gives diameter 6).
Director's own in this round: found that the B-hub half of the hub rule is not needed (a 66-line relaxed set with 30
pairs passed the all-pairs check although 128 slots violated it; the path through the partner's A-hub explains why),
so (13,5) went to 11,636 with card r2c1's 66-point set; q=11 with card r2c2's 87-point set gives 20,713 (beats the table,
23 short of the lab's 20,736); whole-graph annealing with one extra freed point per non-friendly arc at q=9 (11,640 if
it closes) was still running at the time of this entry.
Assessment: the squads contributed the decisive sets (r2c1's 66, r2c2's 87, c1's 51), the explicit family of Lemma 1.3
(r2c10), the routing evidence (c19, r2c5, r2c6), exact small cases (r2c8) and two independent tests of new
propositions (r2c7, r3c4). The new theorems and the record constructions came from the director's own analysis and tools.

## 28 Oct 2026, 20:06-20:55 UTC — job d5-relax (Opus director), squad d5relax-r1 (8 Haiku cards)

Goal: relaxed sets of W(11) with at least 111 points now that pairs may lie on spread lines (Lemma 7.3 of
D5_QUADRANGLE.md, referee point 6): that would beat (15,5) 20,736. Director's tabu before the round: 89 without the
spread condition, 88 with it (the earlier best was 87). Scorer: research/theorems/d5relax/score.py.
Cards (score at q=11): c1 weighted local search with configuration checking (89; q=9 66); c2 unions of orbits of 533
cyclic and 2-generated subgroups of Sp(4,11), exact MIP (best union 81 at order 12, then 89 by tabu); c3 all pairs on
spread lines, restricted model with bound 122 (74, then 89 unrestricted); c4 large-neighbourhood search with exact HiGHS
re-optimisation (89; regions of 700-1000 points solve to optimality and never pass 89); c5 seeded growth from partial
ovoids, Lemma 1.3 and torus orbits (89; two 89-sets share 2 points); c6 algebraic families (graphs of maps, quadrics,
norm conditions; seeds 74-78, then 89); c7 exact SAT at q=5 without the condition (24 undecided after 900 s); c8
memetic search with crossover (89; population collapses to 89 within a minute).
Kept: nothing beyond 89. Director's own: Lemma 7.3 (hub assignment without z not in O), the 20,715 graph over Q(4,11)
with 4 pairs meeting at ovoid points (VALID; rule broken: diameter 6), the order-61 cyclic groups (no relaxed orbit),
the ceilings of Proposition 14.1 (only (15,5) is reachable at all; it needs b >= 111).
Assessment: the squad added no size, but eight unrelated strategies agreeing on 89 (with c4's exact local optimality)
is evidence (not a proof) that 111 is out of reach for this construction.
