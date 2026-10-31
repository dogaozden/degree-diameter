# Squad round sd6-r1 (job selfdual-d6, Oct 31 2026)

Common part of every card (read it first).

**Goal.** A bipartite graph of maximum degree 7 and diameter 6 on more than 9,592 vertices, as a Haar graph H(G,S),
|S| = 7, so |G| = N >= 4,797. H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S. At even D = 6 the
diameter is <= 6 iff S S^-1 S S^-1 S = G (one condition; the "uncovered" count is |G minus that set|).
A *self-dual* S is a union of orbits of psi(x) = u0 beta(x)^-1 (beta an automorphism of G, u0 in G): then the graph
is a bipartite Cayley graph and the uncovered set comes in psi-pairs.

**What we know already (do not repeat).**
- Counting model (research/frontier/SIZE_LAW.md, `research/selfdual-d6/src/count_model.py`): the 7 (1 + 36 + 1296)
  = 9,331 words of S S^-1 S S^-1 S must hit all N elements. A random-like S misses about mu = N e^(-9331/N)
  elements: mu = 18 at N = 1,980, 31 at 2,200, 77 at 2,640, **686 at 4,797**. The first-moment ceiling (mu = 7 ln N)
  is N ~ 2,450. So a record needs an S that is far *better than random*: words of length 5 that collide much less
  than chance and cover G almost evenly (each element about twice). Search over random-like or orbit-symmetric S
  cannot get there; only structure can.
- Calibration (sdhi tabu, 15 s per psi/type): valid self-dual (7,6) graphs at N = 1,512 (PSL(2,7) x Z9), 1,848
  (PSL(2,7) x Z11), 1,980 (PSL(2,11) x Z3; apsp VALID at D = 6), **2,352 (SL(2,7) x Z7, psi(x) = -x^-1, z -> -z,
  type 1+2+2+2; apsp VALID)**. Not yet at 2,184 (PSL(2,13) x Z2 best 2, PSL(2,7) x Z13 best 2), 2,352 for
  PGL(2,7) x Z7 (best 4), 2,640 (PSL(2,11) x Z4 best 17).
- psi = inversion with e in S is a structural trap (the graph is a double cover of a degree-6 Cayley graph). Big cyclic
  factors and small non-abelian parts create word collisions (research/selfdual-hi/README.md: self-dual sets lose
  words at the commuting probability of G).

**Tools** (all in `research/selfdual-d6/src/`, compiled; read the header comments):
- `sdhi K D FACTOR1 [FACTOR2]`: self-dual tabu/enumeration for formula groups (`sl q`, `psl q`, `pgl q`, `meta m k r`,
  `cyc n`); prints `SOL ...` only after a full BFS of the graph. Example:
  `SECS=30 MAXSOL=1 TYPES=1+2+2+2,1+1+1+2+2 timeout 900 nice -n 10 research/selfdual-d6/src/sdhi 7 6 psl 13 cyc 2`.
  `LIST=1` prints the psi options; `PLAIN=1` adds plain (non-self-dual) sets; `ORDS=2,6` adds psi of order 6.
- `haar_sd d D secs seed K OUT.sol GROUP... n` (annealing, about 12x faster per evaluation than sdhi's tabu; G =
  GROUP x Z_n, GROUP = `sl q`, `psl q`, `pgl q`, `meta m k r`, `agl1 q`, `heis q`, `prod G1 G2`, `cyc`):
  plain: `THREADS=1 timeout 900 nice -n 10 research/selfdual-d6/src/haar_sd 7 6 600 1 8 out.sol psl 13 2`;
  self-dual: env `ORBIT="2 m f" SDUAL="tw 1 0"` (f + 2m = 7; QOPT inv|ninv|tw|ntw|meta:A:V:I0:J0);
  orbit-symmetric: env `ORBIT="3 2 1"` (e + two 3-orbits of an automorphism) or `ORBIT="7 1 0"`. A solution file is
  written only after the full two-sided check.
- Checks for any claimed graph: `python3 research/selfdual-d6/src/build_sdhi.py 6 "F1" "F2" "S" out.edges` (sdhi
  sets) or `python3 research/frontier/build_haar2.py SOL.sol out.edges` (haar_sd files), then
  `research/selfdual-d6/src/apsp out.edges 7 6` must print RESULT VALID.

**Machine rules.** About 4 cores and 15 GB are shared by 9 workers: THREADS=1; run anything heavy as
`timeout 900 nice -n 10 <cmd>`; at most about 1.5 GB of memory; no git commits; write only inside your card folder
`research/squads/sd6-r1/<card>/` (you may copy tools there). Time box: about 15 minutes of wall clock in total.
Do not install packages or use the network.

**Report.** Append ONE line of JSON to `research/squads/sd6-r1/scoreboard.jsonl`:
`{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "N_solved": <largest N with a checked
valid graph, or 0>, "best_at_target": <smallest uncovered count at any N >= 4797, or null>, "group": "<spec>",
"valid": true|false, "next": "<one line>"}` and reply in at most 5 lines.

## Cards

- **c1 metacyclic frontier.** Self-dual sdhi on metacyclic C_m : C_k (the (7,5)/(9,5) record shape) between N = 2,100
  and 2,800: list them with `python3 research/selfdual-d6/src/meta_list.py 2100 2800 3 1` (columns N m k r d inv).
  For each group (smallest N first, skip ones with d < 3): `SECS=20 MAXSOL=1 timeout 300 nice -n 10 sdhi 7 6 meta m k r
  cyc 1`. Raise N while you get solutions. Score: the largest N solved.
- **c2 plain vs self-dual, matrix x cyclic.** haar_sd at N = 2,184-2,800 on PSL(2,13) x Z2, PSL(2,7) x Z13 / Z15,
  PGL(2,7) x Z7, PSL(2,17) (2,448), SL(2,13) (2,184), PSL(2,11) x Z4: one plain run and one self-dual run
  (`ORBIT="2 3 1" SDUAL="tw 1 0"` or `ORBIT="2 2 3"`) of 120 s each per group. Which family reaches the larger N?
- **c3 orbit-symmetric S (odd k).** research/structured/STRUCTURE.md says orbits of an automorphism of odd prime order
  k divide the misses by k and double the reachable mu at D = 8. Try it at (7,6): haar_sd with `ORBIT="3 2 1"` (e +
  two 3-orbits) and `ORBIT="7 1 0"` (S = one 7-orbit; needs an automorphism of order 7: PSL(2,q) with 7 | q +- 1 or
  q = 7, or Z_n with 7 | phi(n)), groups of order 2,200-3,000. Score: the largest N solved; then one run at N >= 4,797.
- **c4 psi of order 6.** sdhi with `ORDS=2,6` (self-dual plus an order-3 symmetry: psi^2 is an automorphism-like map of
  order 3); types such as 1+6 and 1+2+2+2 under the order-6 psi. Groups where `LIST=1` shows order-6 psi options:
  PSL(2,13) x Z_n, PSL(2,7) x Z_n, SL(2,7) x Z_n, metacyclic with 3 | k. N = 2,000-3,000. Score: the largest N solved.
- **c5 unipotent / Heisenberg groups (algebraic).** The q-regular "biaffine" part of a generalized hexagon (points and
  lines opposite a flag; Lazebnik-Ustimenko D(5,q)) is a Haar-type graph of a unipotent group of order q^5, and its
  connection set lies on a polynomial curve. Try Haar graphs of p-groups with structured S at (7,6): haar_sd GROUP
  `heis q` (q^3, Heisenberg), e.g. `heis 13` (2,197), `heis 7` x Z14 (4,802 >= 4,797), `heis 5` x Z_n, and if you can
  build them yourself (a small C or Python program), the 5-dimensional unipotent group with S = {e} + 6 points
  (t, t^2, t^3, ...) of a curve, or S on a curve plus 2 extra generators. Measure the uncovered count. Score:
  best_at_target, and the largest N solved. build_haar2.py does not know `heis`: for a claimed graph write your own
  edge-list builder from the solution file (group law (a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab') times Z_n, edges
  (g,A) ~ (s g, B)) and run apsp on it.
- **c6 target-order measurement.** At N >= 4,797 run 10 minutes each: sdhi (all psi, types 1+2+2+2, 1+1+1+2+2) and
  haar_sd plain on SL(2,17) (4,896), PSL(2,17) x Z2 (4,896), PGL(2,17) (4,896), PSL(2,7) x Z29 (4,872),
  SL(2,7) x Z15 (5,040), PSL(2,13) x Z5 (5,460, if time). Report the best uncovered per group and compare with the
  model's mu = N e^(-9331/N) (686 at 4,797; heavy-tailed, the search should land somewhat below mu but not near 0).
- **c7 wildcard.** Find an approach none of the other cards uses (c1 metacyclic self-dual frontier; c2 plain vs
  self-dual on matrix x cyclic; c3 odd-order orbits; c4 order-6 psi; c5 Heisenberg/unipotent; c6 target-order
  measurement; c8 maximize distinct words). It must aim at N >= 4,797 with |S| = 7 and must beat random by structure,
  e.g. S from a subgroup/coset geometry of PSL(2,q) or PGL(2,q), a finite-field polynomial rule in AGL(1,q) x Z_n or
  GF(q^2) : C_k, or a known diameter-6 geometry quotient. Score: best_at_target.
- **c8 wildcard: maximize distinct words.** Instead of the uncovered count, maximize |S S^-1 S S^-1 S| (distinct
  words) in a group of order N >= 4,797 by greedy + local search (write a small C program; one evaluation = 9,331
  products with stamps). The upper bound is 9,331; random S give about N(1 - e^(-9331/N)) ~ 4,110 at N = 4,797. Report
  the best coverage fraction found and how far above random it is; if some group/structure gets > 95 %, say which.
  Score: best_at_target = N - max coverage.
