# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26, new-cells-beyond, round 1 (goal: first checked values for the 48 cells beyond the 2013 table)

Session: Opus director, cloud (session_01V33FTKBcx5tdhhJVPXXVq3), branch claude/new-cells-beyond-etos3t. Files:
research/squads/beyond/r1/ (HEADER.md, c01..c17.md, scoreboard.jsonl, one folder per card). 17 Haiku cards (effort
high), launched together at 15:19 UTC on a 4-core / 15 GB container, each card one cell group or one method, with an
"already found / ruled out" list in the header. Director, in parallel: odd D and fixed generators for haar_big, the Haar
queue (D = 8..12), and the multi-doubled-matching lift (research/frontier/beyond/MDM.md).

Cards (best checked value; all re-checked by the director):
- c01 D=3: PG(2,16), PG(2,17), PG(2,19) (546, 614, 762, Moore) and the fourth hat at q=17 (19,3) 624. No +1 pair (analysis).
- c02 D=4: W(16), W(17), W(19) (8,738, 10,440, 14,480, Moore) and AS(17)+clones (19,4) 10,982.
- c03 (19,4) via Theorem B on Q(4,q) (ovoid clones + shadow lines on a partial spread): reproduces (7,4) 359 at q=5 (21
  lines), but only 54 lines at q=9 where 61 are needed; q=17 still running at the time of writing.
- c04 (20,5) route-chart lift over F5: chart with 22 singular patterns, K3,3 + doubled matching over Z18 (67,500) and
  **Z20 (75,000)**; Z22 stalled at cost 4.
- c05 (19,5), (20,5) DM lifts of W(16), W(17): dmfast reached 0 at q=16 (routes allowed); the director built the lift
  and checked it: **(19,5) 52,428**. q=17 not reported.
- c06 (17,5): Z8 lifts of W(13) with 3 extra matchings, blind annealing, cost in the millions. Nothing.
- c07 (18,5): Z10 lift of W(13) with two doubled matchings, blind annealing of all voltages: cost 7,667, nothing. (The
  director's structured version of the same lift, MDM.md, gives 47,600: ν needs only a parity condition, matchings free.)
- c08 D=6: H(16), H(17) built (hexgen2) and BFS-sampled (≈95 sources each, Moore level sizes); Theorem D at q=17,
  3,203,968 vertices, max eccentricity 6 from 96 sources; q=19 in progress.
- c09 D=7: polygon covers of H(q): full apsp of the builder at q=3, 4 (r=1..3) and sampled BFS of the H(16) instances.
- c10 D=8 2013 pattern: a Z20 lift of H(3)+2 matchings with diameter 8 (14,560 vertices = the pattern's 20·|H(3)| at
  q=3, j=2) found by annealing from cost 2; q=4 stalled at 150.
- c11 (3,11) **1,008** (Haar PSL(2,7)×Z3; metacyclic orders 350–400 fail). c12 (3,12) **1,320** (Haar PSL(2,11)).
- c13 (4,11) **17,600**, (4,12) **48,000** (metacyclic Haar). c14 (5,11) 158,928, (5,12) 229,824, (6,11) 659,568.
- c15 (17,8) **41,373,072** (Haar SL(2,53)×Z139, orbit search); (18..20,8) not reached.
- c16 buildings (Weyl-distance graphs) at max degree ≤ 20, D ≤ 12: nothing above the formula values; D=5 capped at
  31,460. A clean negative.
- c17 wildcard at (18,7): no construction; analysis only.

Kept: the route-chart lift over F5 (c04), the W(16) DM solution (c05), the D=6/D=7 builders (c08, c09), the small
Haar values (c11–c15). Learned: blind annealing of lifts of W(13) fails (c06, c07) while the structured lift with one
parity condition works in seconds (director). Next: round 2 evolves the route charts ((20,5) push, 5×F4, 6×F3, 9×F2,
plain letters for (17,5), (19,5)), tries the MDM lift of W(8) for a (13,5) record, referees MDM, pushes the cubic and
quartic D=11/12 cells, and checks the literature.
