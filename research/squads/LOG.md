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
