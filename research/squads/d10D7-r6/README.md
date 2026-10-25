# d10D7 squad round 6: structured starts for tabu search (partial ovoids of H(8); non-collinear sets of H(9))

Background: research/squads/d10D7-r5/README.md. The (10,7) record is now **225,128 = 6·37,449 + 2·217**. Here
K = 217 is the size of a set of pairwise opposite points of H(8) (research/d10D7/sets/P8_r5c4_217.txt). Every
extra point adds 2 vertices.

Round-5 lesson (card c4). A plain k-fixed tabu search from random greedy starts stalls at 80-134. Started instead from
a **structured set**, the same tabu reached 217 in 170 s. That set was 31 orbits (93 points) of the order-3 subgroup
T_3 of the norm-1 torus (order 513) of W(5,8), found by a tabu search on the orbit graph. The final 217 set keeps
almost none of the T_3 symmetry: only 3 of its points map into the set under the T_3 shift. So the structured core
seems to act as a good basin, not as a template. Upper bounds: a partial ovoid of W(5,8) has at most 457 points
(project from a hyperbolic line spanned by two of its points), so there is room.

Same story at q = 9 for the (11,7) spin-off, 407,134 = 6·66,430 + 2·4,277. That set is 47 orbits of an order-91
element (research/squads/d10D7-r5/c6). The set has no two points collinear. Distance-2 ovoid bound: 6,643.

## Tools (copy into your folder; do not edit others' folders)
- research/squads/d10D7-r5/c4/: common.py (W(5,8) coordinates, B form, orbits), run_orb.py (orbit graphs: T3, T9,
  T19, T27, ..., L73), mis_csr.c (tabu MIS on an orbit conflict graph), pov2.c (k-fixed tabu on H(8) points with an
  INITFILE start: `./pov2 HEXBIN SEED SECS OUT TA TB STALL PERT RESTART ADDFREE INITFILE`, c4 used
  `7 10 200000 5 1000000000000 0 INIT`), T3_conf.bin (orbit graph, 165 MB, already built), T3_mis_s1.txt (the
  93-point core), L73_core_*.txt (7 cores of 73 points of the order-73 Levi torus).
- research/squads/d10D7-r5/c6/ (q = 9): grp.py, orb.py, qtabu.py (order-91 orbits); research/squads/d10D7-r4/c4/mis.c
  (k-fixed tabu for non-collinear sets of H(9), with INIT option; see its source).
- Scorer, the only thing that counts: `research/squads/d10D7-r4/tools/setcheck research/d10D7/hex/hex_q8.bin FILE
  points opposite` (q = 9: `... hex_q9.bin FILE points noncollinear`) → "VALID size S".

## Rules
4 cores and 15 GB are shared by Opus and up to 8 cards. Run heavy commands as `timeout <=1700 nice -n 10 ...`, ONE
process at a time, < 1.5 GB RAM. Work only in research/squads/d10D7-r6/<card>/. No git commits. Save your best set as a
plain id file. Time box: about 40 minutes. At the end, append ONE JSON line to research/squads/d10D7-r6/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "file": "<best set>", "command": "<exact>", "score": <size>,
"metric": "partial_ovoid_H8" or "noncollinear_H9", "valid": true|false, "next": "<one line>"}, then reply in at most 5 lines.
