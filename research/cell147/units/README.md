# (14,7): the polygon cover GH(11) + 2 matchings over Z5 with "units"

Session cell-14-7 (Opus), 2026-10-24. Cell (14,7): bipartite, maximum degree 14, diameter 7. Table value 1,771,560
(Delorme-Gomez-Quisquater: GH(11) incidence graph + 2 point->line perfect matchings, lifted by Z5; polygon edges
voltage 0, matching t voltage t; research/lifts/LITERATURE.md section 5 on branch claude/voltage-lifts-search-6lfotq).

## The unit

A unit (p, t) on that lift deletes the 5 lifted copies of the matching edge (p, l), l = sigma_t(p), and adds two new
vertices: z joined to the 5 copies (p, c) and z' joined to the 5 copies (l, c). Degrees stay <= 14 (z, z' have degree
5). Net +2 vertices.

Why the diameter can stay 7. In the DGQ lift every pair has a route using at most one matching edge, located at the
source, at the target, or at a neighbour of the source (with q+1 choices of neighbour). Deleting (p, l) in every copy
therefore only breaks
1. routes from (p, c) to points opposite p (hexagon distance 6) in copy c + h_t (everything else in that copy is
   reached through z: (p,c) - z - (p,c+h_t) then <= 4 or <= 5 hexagon steps), and
2. routes from (l, c + h_t) to lines opposite l in copy c (dually, through z').
Repair of 1: for a line M through p, the 14,641 lines at distance 4 from M whose projection onto M is not p partition
the 161,051 points opposite p (11 each). If sigma_t maps points at distance 4 from p onto those lines, every opposite
point y has the route (p,c) -4-> (x,c) -hop-> (sigma_t(x), c+h_t) -1-> (y, c+h_t) of length 6. Dually for 2 with the
points at distance 4 from a point N of l whose projection is not l. DGQ is valid for any matchings, so prescribing
sigma_t on these sets costs nothing; a greedy assignment always exists (|A&B| = |F1&C| in every case tried).
The cyclic shift of copies is an automorphism fixing z and z', so it suffices to check the sources (x, 0) and z, z'.

## Result: 1,771,562 vertices (one unit)

- State (matchings): `u11_one.state.gz` (glift state format: header, then per point "sigma_1 h_1 sigma_2 h_2",
  then per line its flag voltages, all 0); unit file `u11_one.units` ("1000 1": point 1000, matching 1).
- Build:
  ```
  cd research/cell147 && gcc -O2 -o gh_build gh_build.c && ./gh_build 11 > data/gh_11.txt   # sha256 e3a4d834...6eb9d
  cd units && gunzip -c u11_one.state.gz > u11_one.txt
  python3 unit_edges.py ../data/gh_11.txt u11_one.txt u11_one.units u11_one.edges        # sha256 5375337d...fd97f30
  ```
  The edge list has n = 1,771,562 vertices and 12,400,925 edges (first line n, then "u v").
- Check (`ucheck12`, written for this job from the definitions, all 354,312 base sources plus the 2 unit vertices,
  every lift vertex being equivalent to one of them under the cyclic shift): `d14D7_n1771562_ucheck.txt`:
  pairs beyond distance 7 = 0. The same checker agrees with apsp on the small cases below (valid and invalid).

## Small cases checked with apsp (all-pairs, no symmetry assumed)

| base | units | vertices | Delta | apsp |
|---|---|---|---|---|
| GH(3) + 2 matchings over Z5 | 1 | 3,642 | 6 | VALID D=7 |
| GH(5) + 2 matchings over Z5 | 1 | 39,062 | 8 | VALID D=7 |
| GH(5) + 2 matchings over Z5 | 2 (far apart) | 39,064 | 8 | INVALID D=8 (new vertices too far apart; ucheck agrees) |
| GH(5) + 2 matchings over Z5 | 20 (clustered, udesign) | 39,100 | 8 | VALID D=7 |
