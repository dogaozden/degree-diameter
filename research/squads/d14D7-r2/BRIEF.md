# Squad brief: cell (14,7) and the D = 7 hexagon cells, round 2

You are one card of a 16-card Haiku squad run by Opus (session cell-14-7, second session, 2026-10-24). Work only in your
card folder `research/squads/d14D7-r2/<card>/` (create it). No git commits. Never contact anyone or post anything
outside the repo. Read this brief, then your card.

## What is known (read this, it saves you time)

- Table graphs (Delorme–Gómez–Quisquater, "DGQ"): take the incidence graph of the split Cayley hexagon H(q) (points
  P, lines L, |P| = |L| = (q^6-1)/(q-1), (q+1)-regular, diameter 6), add j perfect matchings sigma_1..sigma_j from points
  to lines, lift by Z_m with m = 2j+1 (hexagon edges voltage 0, matching t voltage t). Degree q+1+j, diameter 7, for
  ANY matchings. (14,7) = q=11, j=2: 5 x 354,312 = 1,771,560.
- A UNIT (p, t) deletes the m lifted copies of the matching edge (p, l), l = sigma_t(p), and adds two "hubs":
  z joined to the m copies of p, z' joined to the m copies of l (+2 vertices). Hubs have m edges, so Delta - m spare
  slots, which we use for a "hub graph" (links z_i ~ z'_k) that keeps hubs of the same side within distance 6.
- NEW today (Opus): the TYPE-2 DESIGN makes a unit valid with only q^2 assignments. Take l THROUGH p (an incident
  flag). W = the q^2 points collinear with p but not on l; K = the q^2 lines meeting l but not through p. If sigma_t
  maps W onto K (any bijection), both unit endpoints reach everything within 7 (routes of length 6:
  (p,0) -2- (w,0) -hop- (K,h) -3- (y,h) for every point y opposite p, and dually). Proof in t2design.c's header.
- Units on the SAME matching must have disjoint "zones": point zone {p} ∪ W (q^2+1 points) and line zone {l} ∪ K
  (q^2+1 lines). Units on different matchings never conflict. So the number of units per matching is a PACKING
  problem: pack as many flags as possible with pairwise disjoint point zones and pairwise disjoint line zones.
  Zones meet when freed points are at distance <= 4 (in H(q)), except "chained" pairs: d(p,p') = 4 is fine when the
  connecting path leaves p along l (or p' along l'). Pairwise opposite freed points (distance 6) never conflict on
  the point side. Two points of H(q) are at distance <= 4 iff they are orthogonal on the quadric Q(6,q).
- Current best for (14,7): random packings reach about 75-80 flags per matching at q = 11 (theoretical cap 1,452).
  With the same flag set on both matchings, n = 1,771,560 + 4N for N flags per matching. 155 units (n = 1,771,870) are
  being fully checked by Opus.
- Demo: (7,7) with 28 type-2 units: 23,492 vertices, VALID (current record 23,484).

## Tools (all in research/cell147/units/ unless noted; compiled; run them from that folder)

- `../data/gh_Q.txt` for Q = 3, 5, 7, 11 (format "P q", then one line per hexagon line with its q+1 point ids; points
  are 0..P-1, lines are numbered by row). Build others: `../gh_build Q > FILE` (Q prime), Q = 9:
  `gcc -O2 -o hexgen /home/user/degree-diameter/research/p4/d6/hexgen.c && ./hexgen 9` (writes hex/hex_q9.bin; run it in
  your folder), then `python3 hexbin2txt.py hex/hex_q9.bin > gh_9.txt`.
- `pack GHFILE SECONDS SEED OUTFLAGS [INFLAGS]`: simulated annealing for packings of flags (output lines "p l", l a
  line index). Env: GROW=n (compact growth from n seeds first), LAM0 LAM1 T0 T1 (schedules). Source pack.c.
- SCORER for packings: `CHECKONLY=1 ./pack GHFILE 0 1 /dev/null FLAGS` prints `VALID N flags ...` (N = your score).
- `t2cell.sh NAME GHFILE j DELTA SEED THREADS [FLAGS]`: builds the whole graph for a DGQ cell (random matchings,
  type-2 units from FLAGS on every matching, or a random scan packing without FLAGS; random hub graph) and checks it
  with `uhcheck` (all sources; prints "pairs beyond D = 0" when valid). QUICK=1: check only unit endpoints and new
  vertices (enough when the design is exact; use it for q >= 11). Output files in cells2/ (copy them to your folder,
  and use a NAME starting with your card id, e.g. c9_try3).
- `uhcheck GHFILE STATE UNITS EXTRAS D THREADS` (hub-aware diameter checker), `unit_edges2.py` (edge list),
  `apsp_cyc` (independent check of an edge list: `NB=<2*P*m> ./apsp_cyc EDGES Delta 7 m THREADS`), `t2design.c`,
  `randhub.py`, `mkunits.py`. Read their headers.

## Machine rules (4 cores, 15 GB shared by 16 cards and Opus)

- Anything longer than ~20 s goes through the slot semaphore:
  `/home/user/degree-diameter/research/squads/bin/heavy.sh SECONDS <command...>` (adds timeout and nice; waits for one
  of 3 machine-wide slots). THREADS=1 always. At most ~1.5 GB memory per run.
- Time box: about 25 minutes of wall clock in total. No edits outside your card folder (copy tools there to modify
  them). No git.

## Report

Append ONE line of JSON to research/squads/d14D7-r2/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "unit": "<what the score is>",
 "valid": true|false, "next": "<one line>"}
and reply to Opus in at most 5 lines. A claim must come with files Opus can check (flags file, or cells2-style
state/units/extras files, plus the exact command).
