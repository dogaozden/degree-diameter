# Squad d16D8 round 3: common brief (read this first, then your card)

LONG GOAL: beat the bipartite (16,8) record 36,201,060 = 45 copies of the incidence graph I of the generalized hexagon
H(13) with 2 extra edges per vertex (Delorme–Gómez–Quisquater, unpublished). Their family: m = 5·⌊(q+5)/2⌋ copies of
I(H(q)), degree q+3, diameter 8: q=3: 20, q=5: 25, q=7: 30, q=13: 45.
Model: a Z_m-lift of I + 2 perfect matchings (points -> lines); vertex (x,g), g in Z_m; diameter 8 wanted.

WHAT WORKED IN ROUND 2 (testbed W(q) at diameter 6): (a) designs invariant under a semiregular cyclic collineation
group C (one voltage per C-orbit of edges, C-equivariant matchings): q=13 m=28 vs 14 for random; (b) targeted repair
(take an uncovered (source, target, sheet), change one voltage on a short walk so it is covered; Metropolis): m=23.
THIS ROUND combines them ON THE HEXAGON ITSELF. Opus built the tools and tested them:
- H(5) with C of order 31 (126 point orbits, 252 source orbits), H(7) with C of order 19 (2,064 source orbits),
  H(3) with C of order 13 (56 source orbits). A random C-invariant design at H(3), m = 20 is already VALID.
- Side records: 27 copies of H(5) = 210,924 would beat the (8,8) record 206,448; 31 copies of H(7) = 1,215,696
  would beat the (10,8) record 1,176,480. DGQ's own counts at q = 5, 7 are 25, 30.

TOOLS (in /home/user/degree-diameter/research/d16D8/, already built; do not edit; copy into your folder for variants):
- `python3 symbase.py hex q hex/sym_qQ_rR.json m seed OUT.base OUT.src` -> random C-invariant design + orbit sources.
  Groups: hex/sym_q3_r13.json, hex/sym_q5_r31.json, hex/sym_q7_r19.json (made by hexsym.py; "pt"/"ln" are the
  generator's permutations of points 0..N-1 and lines 0..N-1). Base vertex ids: point p = p, line l = N + l.
  For W(q): `python3 symbase.py gq 13 /home/user/degree-diameter/research/squads/d16D8-r2/c4/group_q13.json m seed OUT OUT.src`
  (group_q7.json, group_q11.json also exist). In the .base file the 4th field of each edge = its orbit id.
- `SRCFILE=OUT.src ./symrepair OUT.base D SECS SEED BEST.base` : targeted repair keeping C-invariance (all edges of an
  orbit share one voltage); prints progress to stderr; writes BEST.base. env T0, T1, K, NODES (see symrepair.c header).
  D = 8 for hexagons, 6 for W(q). With SECS = 0 it only evaluates.
- `SRCFILE=OUT.src ./baselift eval FILE D` : exact check of a C-invariant design from the orbit sources (fast).
  `./baselift eval FILE D` (no SRCFILE): check from ALL sources. A VALID claim needs this full check printing
  "VALID(all sources)" (H(5): ~2 s, H(7): ~1 min, W(13): ~2 s).
- Hexagon files: hex/hex_q3.bin, hex_q5.bin, hex_q7.bin (int32 q, N, L, then L*(q+1) point ids, then N*7 coords).
- Warm start idea (round 2, card c1): map a VALID Z_m design to Z_(m+1) by keeping voltages (identity map) and repair.

MACHINE RULES (4 cores, 15 GB shared by 9 agents): THREADS=1; anything longer than a few seconds as
`timeout 1500 nice -n 10 <cmd>`; at most ONE heavy process at a time; <= 1.5 GB memory; no git; write only inside your
card folder /home/user/degree-diameter/research/squads/d16D8-r3/<card>/. Time box: about 25 minutes of work.

REPORT: append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/d16D8-r3/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "polygon": "H(5)|H(7)|H(3)|W(13)|...", "score": <largest VALID m>,
 "valid": true|false, "best_design": "<path>", "command": "<exact full check command>", "next": "<one line>"}
(add other fields if your card asks). Only claim VALID after the full all-source check. Reply to Opus in <= 5 lines.
