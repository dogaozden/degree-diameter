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
