# Squad c157b-r1 (job cell-15-7, resume session, 2026-10-25): common brief

## Goal
Raise the (15,7) record (now 2,500,147 on our branch; table 2,480,184). The graph is 14 * 177,156 + R_H + R_L + 4m:
seven copies of the incidence graph of the generalized hexagon H(11) plus hub vertices. You improve ONE of the sizes:
- **R_H**: a set of POINTS of H(11) with no two on a common line (a "non-collinear set", partial distance-2 ovoid).
  Current best 8,645 (65 orbits of an order-133 collineation). Upper bound 14,763 (= 177,156/12). Each extra point = +1.
- **R_L**: a set of LINES with no two through a common point ("non-concurrent set"). Current best 8,246. Each extra = +1.
- **m**: a mirrored set (R', sigma), see card c7. Current 768. Each extra element = +4.

## Data (all in research/squads/c157b-r1/shared/; do not edit, copy what you need into your folder)
- `hex_q11.bin`: H(11). int32 q=11, N=177156, L=177156; then L*12 int32 = the 12 point ids on each line (line l at
  offset 12*l); then N*7 uint8 = coordinates of each point in PG(6,11) on the quadric X0X4 + X1X5 + X2X6 = X3^2
  (first nonzero coordinate 1, rows sorted by the base-11 code sum X_i 11^i). Every point is on 12 lines, every line
  has 12 points. Two points are collinear iff some line contains both.
- `RH.txt` (8,645 points), `RL.txt` (8,246 lines): the current best sets (ids, one per line).
- `g133_pts.txt`, `g133_lines.txt`: the permutation of points / lines (image of id i on row i) induced by the order-133
  collineation g = [[8,1,10],[0,8,1],[7,4,4]] in SL(3,11), acting as (v, a, w) -> (g v, a, g^-T w) with v = (X0,X1,X2),
  a = X3, w = (X4,X5,X6). It is fixed-point-free: 1,332 orbits of 133 on points and on lines. RH and RL are unions of
  its orbits.
- `gperm.py`: makes such permutations for ANY collineation: `python3 gperm.py sl3 a b c d e f g h i OUT` for g in
  SL(3,11), or `python3 gperm.py mat7 <49 entries> OUT` for a 7x7 matrix over F_11 (it checks that lines go to lines).
  Also importable (perm_from_mat7, sl3_to_mat7, orbit_sizes). Known extra collineation: (v, a, w) -> (w, -a, v).
- `chkset.py`: THE SCORER. `python3 research/squads/c157b-r1/shared/chkset.py P yourset.txt` (points) or `... L ...`
  (lines) prints `VALID P <size>` or `INVALID ...`.
- Existing local search (C): research/d15D7b/pack.c (ILS with (1,k)-swaps; `gcc -O2 -o pack pack.c`;
  `./pack HEXBIN P|L SEED SECONDS [START] OUT`). From random starts it reaches ~7,200 points in 2 minutes; from RH.txt it
  finds nothing in 2 minutes. The symmetric (orbit) search that found RH is much stronger than plain local search, so
  structure matters.
- Earlier orbit-search code (order-61 / order-133 groups, research/squads/cells/d16D7/orbset.c, ogquot.py) may help.

## Rules (shared machine: 4 cores, 15 GB, shared with 7 other cards and Opus)
- Work ONLY in your folder research/squads/c157b-r1/<card>/ . No git commands. No edits elsewhere.
- One thread per program. Prefix heavy runs with `timeout 1200 nice -n 10`. At most 1.5 GB memory.
- Time box: about 25 minutes of wall time in total. Write C for anything that loops over all 177,156 elements many times.
- Save your best set as <card>/best_P.txt or <card>/best_L.txt (ids, one per line), and check it with chkset.py.
- At the end append ONE line of JSON to research/squads/c157b-r1/scoreboard.jsonl:
  {"card": "c3", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <size>, "kind": "P|L|m",
   "valid": true|false, "next": "<one line>"}
  and reply in at most 5 lines (best score, file, one-line idea, what to try next).
