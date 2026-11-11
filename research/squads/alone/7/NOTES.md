# squad-alone-7 (wildcard): notes

Goal: a bipartite graph with max degree 16, diameter 5 and more than 31,460 vertices.
**Result: no candidate beat 31,460.** Nothing valid was found. Every candidate that claimed to be a graph of diameter 5
was checked by an independent all-pairs computation (research/theorems/coordinator_check/apsp.c) and failed.
What I can report with confidence is one impossibility result for covers of the record, a measured wall for Haar
graphs near this order, and a new family (bi-coset graphs with non-regular sides) that reaches 32,760 vertices but
still has diameter 6.

## 1. Covers of the flag graph cannot have diameter 5 (proved; two independent computations)

Base X = flag graph of PG(4,3) (31,460 vertices, degree 16; coordinator build, check in
research/theorems/coordinator_check/check_d16D5_31460.txt).

Structure I checked first (my first guess, that X has girth 6, was wrong): each edge lies in exactly one K(4,4)
block, indexed by a (line, plane) pair with line < plane. There are 377,520 ordered pairs of vertices with 4 common
neighbours (girth_check.py), so X has 4-cycles.

Lemma. Let H -> X be a connected covering with fibre size k >= 2 (a local bijection; a regular cover is a special
case). Take a vertex u of X and a same-side vertex v. Shortest paths in H are non-backtracking, and a non-backtracking
walk in H projects to a non-backtracking walk in X, with the lift unique given the start. So the number of preimages
of v within distance 4 of a fixed preimage of u is at most the number of non-backtracking walks of length <= 4 in X from
u to v. Preimages of v lie on v's side, so their distance is even, and diameter 5 forces it to be <= 4. Hence every
same-side pair needs at least k such walks.

Computation (walks.py, cover_check.py: DP and explicit DFS agree). From one vertex on each side (PGL(5,3) is transitive
on each side, so one source per side suffices): 54,096 non-backtracking walks of length 2 or 4 land on the 15,729
same-side vertices; 11,664 of them receive exactly one walk. Therefore no connected covering of X with fibre size
>= 2 has diameter <= 5. This rules out every lift and every cover of the 31,460 record. It does not rule out a
different graph of the same order.

Remark (random-model check). Under independence, a same-side vertex would receive Poisson(3.44) walks: P(0) = 3.2 %
and P(1) = 11 %. The flag graph has no target with 0 walks, 11,664 with exactly 1 and 2,916 with exactly 4 (about 93 %
of targets). That is a much tighter, more regular cover than random, which is the kind of structure a new record would
need.

## 2. Haar wall near this order (calibration, haar_gen3 as shipped)

d = 16, D = 5, group psl 13 x Z_n, annealing, THREADS = 4 (scoreboard lines 2-4):

| N = |G| | vertices | best uncovered | run |
|---|---|---|---|
| 8736 | 17472 | 1 | 60 s |
| 13104 | 26208 | 167 | 60 s |
| 16380 | 32760 | 621 | 90 s |

The uncovered count at 16380 (621) matches the size-law prediction for random-like S (about 600). At N = 8736 the
search reached 1 uncovered and no zero in 60 s. Above that, the counts are far from zero. Random-like Haar annealing
therefore does not look able to reach N = 15,731 (31,462 vertices), but I ran only three short calibration runs.

## 3. Bi-coset graphs with non-regular sides (new family; not a record, diameter 6)

bicoset.py. G = SL(2,64). A, B are subgroups of order 16 of the unipotent radical (4-dim F2-subspaces of GF(64)).
Vertices are right cosets Ag and Bh, with Ag ~ Bh iff gh^-1 in A x B for a fixed x in G. Degree = |A : A cap xBx^-1|
= 16 when the intersection is trivial (checked). Right multiplication by G is transitive on each side, so the diameter
is max(ecc(A.1), ecc(B.1)). With N = 16,380 per side this gives 32,760 vertices, above the record.

- Random probe (seed 1): connected, degree 16 everywhere, eccentricity 6 from both sides. Histogram from A.1:
  dist 4: 15288, dist 5: 13178, dist 6: 851. apsp.c: diameter 6, RESULT INVALID.
- Simulated annealing over (VA, VB, x), cost = number of vertices at distance >= 6 from A.1 and B.1: four chains,
  about 100 steps each. Best cost 918 (chain 3). apsp.c on that candidate: diameter 6, RESULT INVALID.
- Interpretation: the far-vertex count is about N e^(-W/N), with W = 54,240 walks of length <= 4, which gives about
  600 per side, so about 1,200 in total. The search only reaches about 900. The family behaves like a random model,
  not like the flag graph. The search space here is small (about 651^2 subspace pairs times the double cosets of x),
  so 400 evaluations are a small sample. I did not exhaust it.

## 4. What I did not do, and why

- Other rank-4 building types. I argued (not computed) that degree 16 with the bipartition {1,3} / {2,4} forces q = 3
  with the split rank-4 type A_4, since the residues have size (q+1)^2 = 16. The argument for the other rank-4 types
  (F_4(3), B_4, C_4) is that their double-coset lengths make the diameter well above 5. Neither was computed. Testing
  them needs Chevalley-group double-coset code (GAP or similar), which is not available here.
- Bigger groups with larger subgroups (|A| = 32 with N = |G|/32, PSL(2,81) with dihedral subgroups). Not run.
- Longer annealing on the bi-coset family. Four 8-minute chains are not enough to exclude diameter 5 there.

## 5. Files

- walks.py, cover_check.py: non-backtracking walk multiplicities of the flag graph (section 1).
- girth_check.py: 4-cycle count (section 1 correction).
- bicoset.py, search.py, build_edges.py, hist_probe.py: bi-coset family (section 3). build_edges.py writes the edge
  list for apsp.c.
- runs/sa_*.out, runs/sa_*.log: annealing outputs. runs/probe_*.edges was moved out of the repo (about 3 MB).
- scoreboard.jsonl: one line per serious attempt (7 lines).
- Edge lists and haar_gen3 solution files are in the scratchpad, not committed.
