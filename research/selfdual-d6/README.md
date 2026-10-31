# selfdual-d6: self-dual (bipartite Cayley) Haar graphs at diameter 6

Job "selfdual-d6" (Opus cloud session, Oct 31 2026, from 08:30 UTC). Method of `../selfdual-d5/README.md` and
`../d75-raise/README.md` taken to D = 6, in the cells where no generalized hexagon exists (Delta - 1 not a prime
power). Targets (ours, from Delorme's hexagon doubling and our Theorem D; table in parentheses): (7,6) 9,592 (8,992),
(11,6) 148,944 (142,464), (13,6) 388,972 (374,452), (15,6) 870,440 (842,048), (16,6) 940,846 (884,062).

## Result

**No record.** No Haar graph (self-dual or plain) comes near any D = 6 target. The largest valid (7,6) Haar graphs
found have N = |G| = 2,352 (4,704 vertices; SL(2,7) x Z7 with a self-dual S, and PSL(2,7) x Z14 with an
orbit-symmetric S), half of the 4,797 that (7,6) needs. At the target order every method tried (self-dual tabu,
plain and orbit-symmetric annealing, seven group families, a direct maximization of distinct words) stops at 437-505
uncovered elements out of about 4,900. The counting model below predicts exactly this: the D = 6 targets lie far
above the first-moment ceiling for Haar graphs, (7,6) by a factor of 2 in N and the other cells by more. A Haar graph
there would need a connection set much better than random (words of length 5 covering G almost evenly, about twice
each), i.e. an algebraic construction; none of the structured families tried here (Heisenberg groups, AGL(1,q) with
polynomial S, psi of order 6, orbits of order 3) is better than random by more than the usual factor.

## The test at diameter 6

H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S, |S| = K. Right multiplication by G is transitive on each
side. From (e,A), side B within distance 1, 3, 5 is S, S S^-1 S, S S^-1 S S^-1 S. So

  diam H(G,S) <= 6  iff  S S^-1 S S^-1 S = G,

and this one condition already gives the same-side conditions ((S^-1 S)^3 = S^-1 (S S^-1 S S^-1 S),
(S S^-1)^3 = (S S^-1 S S^-1 S) S^-1). This is the D = 6 form of the side-A test of selfdual-d5 (there X X = G,
X = S^-1 S, distance 4; here the cross test at distance 5). Unlike D = 5, self-duality removes no condition at
D = 6. What it does: if psi(S) = S for psi(x) = u0 beta(x)^-1, then psi(S S^-1 S S^-1 S) = S S^-1 S S^-1 S, so the
uncovered elements come in psi-pairs (the effective Poisson mean is about mu/2 plus the psi-fixed misses), and the
graph is a bipartite Cayley graph (vertex-transitive).

## Counting model (`src/count_model.py`, the model of `../frontier/SIZE_LAW.md`)

The W = K (1 + (K-1)^2 + (K-1)^4) words of S S^-1 S S^-1 S must hit all N elements; a random-like S misses about
mu = N e^(-W/N). N_h is the first-moment ceiling (mu = K ln N: about N^K sets, each succeeds with probability about
e^(-mu)); N_wall is where mu equals the fitted search wall mu*(N) of SIZE_LAW (ln mu* = 4.34 - 0.123 ln N).

| cell | ours | N needed | W | W/N | mu at N needed | N_h (2 N_h vertices) | N_wall (2 N_wall) |
|---|---:|---:|---:|---:|---:|---:|---:|
| (7,6) | 9,592 | 4,797 | 9,331 | 1.95 | 686 | 2,453 (4,906) | 2,175 (4,350) |
| (11,6) | 148,944 | 74,473 | 111,111 | 1.49 | 16,751 | 21,117 (42,235) | 16,861 (33,722) |
| (13,6) | 388,972 | 194,487 | 271,453 | 1.40 | 48,165 | 46,708 (93,417) | 36,414 (72,829) |
| (15,6) | 870,440 | 435,221 | 579,195 | 1.33 | 115,013 | 92,132 (184,263) | 70,644 (141,288) |
| (16,6) | 940,846 | 470,424 | 813,616 | 1.73 | 83,437 | 125,137 (250,274) | 95,324 (190,649) |

Even the table values (8,992 etc.) are above N_h in every cell: random-like Haar graphs cannot reach them. The
earlier d6haar job (`../p4/d6haar/REPORT.md`) came to the same conclusion with plain annealing; self-duality and orbit
symmetry move the search wall towards N_h (the frontier below is at mu = 45 against mu* about 27), not past it, since
the number of symmetric sets shrinks by as much as the success probability grows (`../structured/STRUCTURE.md` §1).
The selfdual-d5 records were possible because at odd D the self-dual family removes one of the two conditions, which
halves mu; at even D there is only one condition to begin with.

## Calibration (the tabu finds valid graphs below the frontier)

sdhi tabu, K = 7, D = 6, every psi option (involutions modulo inner automorphisms) and type, 15 s per psi/type
(`logs/calib/`):

| group | N | vertices | mu | sols | best |
|---|---:|---:|---:|---:|---:|
| PSL(2,7) x Z9 | 1,512 | 3,024 | 3 | 24 | 0 (most psi/types solve in < 0.1 s) |
| PSL(2,7) x Z11 | 1,848 | 3,696 | 10 | 15 | 0 |
| PSL(2,11) x Z3 | 1,980 | 3,960 | 18 | 24 | 0 |
| PSL(2,7) x Z13 | 2,184 | 4,368 | 31 | 2 | 0 (psi(x) = (hxh)^-1, h = diag(1,3) (outer), z -> -z, type 1+2+2+2) |
| PSL(2,13) x Z2 | 2,184 | 4,368 | 31 | 0 | 2 |
| SL(2,7) x Z7 | 2,352 | 4,704 | 45 | 1 | 0 (psi(x) = -x^-1, z -> -z, type 1+2+2+2) |
| PGL(2,7) x Z7 | 2,352 | 4,704 | 45 | 0 | 4 |
| PSL(2,11) x Z4 | 2,640 | 5,280 | 77 | 0 | 13 |

Checked hits (sdhi CHECK, `src/build_sdhi.py` from the printed formula, apsp; `logs/calib/check/`, edge lists
gzipped, sha256 in `sha256.txt`):
- PSL(2,11) x Z3, N = 1,980: S = [1 7 9 9]|1 [2 7 9 10]|2 [1 6 10 6]|0 [5 6 10 10]|0 [2 9 0 6]|1 [5 9 0 9]|2
  [1 2 10 10]|0 (psi(x) = x^-1, z -> -z, type 1+2+2+2). apsp RESULT VALID at D = 6 (n = 3,960), INVALID at D = 5;
  build_sdhi.py: VALID, edge list identical.
- SL(2,7) x Z7, N = 2,352: S = [1 3 5 2]|0 [5 3 5 6]|0 [0 5 4 3]|4 [4 5 4 0]|3 [0 4 5 4]|5 [3 4 5 0]|2 [0 6 1 0]|0
  (psi(x) = -x^-1 on SL(2,7), z -> -z on Z7, so beta = identity and u0 = (-I, 0); type 1+2+2+2, the fixed element
  [0 6 1 0]). apsp RESULT VALID at D = 6 (n = 4,704), INVALID at D = 5; build_sdhi.py: VALID, edge list identical.
  Conventions as in sdhi.c / build_sdhi.py: [a b c d] is the matrix with rows (a b), (c d) over GF(7), "|z" the Z7
  coordinate, (g,A) ~ (s g, B).

## Squad round sd6-r1 (`../squads/sd6-r1/`, `../squads/LOG.md`)

Eight Haiku cards, 15 minutes: metacyclic self-dual frontier (largest solved 2,107; 2 uncovered at 2,325), plain vs
self-dual haar_sd on PSL/PGL(2,q) x Z_n (tie at 2,184), orbit k = 3 (solved 2,352 = PSL(2,7) x Z14, re-checked here
with build_haar2.py + apsp; 505 at 5,208), psi of order 6 (none; an order-6 map on Z_n confines the short orbits to a
subgroup), Heisenberg groups (Heis(13), 2,197, solved; 481 at Heis(17), 4,913), AGL(1,q) with polynomial S (quadratic
S worse than random; 485 at 4,970), target-order measurement on six groups (best 448, SL(2,17)), and a direct
maximization of |S S^-1 S S^-1 S| (best 91.1 % = 437 uncovered on SL(2,17), random S 82.8 %).

## Frontier and target runs (`logs/front/`, `logs/target/`, `logs/k11/`)

(Filled in at the end of the job.)

## Tools (src/)

`sdhi.c`, `haar_sd.c`, `build_sdhi.py`, `meta_list.py`, `sweep.py`, `hsd_queue.py` are copied unchanged from the
selfdual-hi job (branch claude/selfdual-haar-d7-d8-rwwjp8, `research/selfdual-hi/src/`), which already wrote them for
any D: at even D = 2k the energy is the number of side-B elements outside S X^(k-1), X = S^-1 S, i.e. the test above.
Read their header comments. sdhi handles factors of at most 8,192 elements (multiplication tables), so the (11,6)
runs use haar_sd only. New here: `count_model.py` (counting model at D = 6), `runq.py` (run a file of shell lines,
P at a time). `apsp` = research/lifts/coordinator_check/apsp.c.
