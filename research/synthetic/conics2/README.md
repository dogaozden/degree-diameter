# conics-2: the freed sets of CONICS.md 3.4 on every diameter-7 cell built on a generalized hexagon

Job "conics-2" (29 October 2026), follow-up to job "conics" (research/synthetic/CONICS.md, Section 3.4, branch
claude/conics-generalized-polygons-6gjqxi, merged into this branch). Every statement is labelled **Theorem** (proved
here or in the cited note), **Computer-checked** (a program checked it; the program is in the repository) or
**Heuristic**. Notation as in D7_HEXAGON.md (branch claude/d7-hexagon-theorems-4w1prt): levels of type H (a copy of the
incidence graph of H(q)) and D (its dual), friendly transitions (types differ, identity matching), non-friendly ones
(the mirrored local duality sigma of the lab's records), freed sets, hubs, Theorem 3.4.

## 1. Results

| cell | q, levels | before this job (master / job "conics") | this job | hubs per side | hub graph | all-pairs check |
|---|---|---:|---:|---|---|---|
| (14,7) | 11, HDHDH | 1,789,588 / 1,802,400 | **1,802,642** | 15,541 + 15,541 | random, degree 9 | passed (all sources, one local run) |
| (15,7) | 11, HHDHHDD | 2,501,491 / 2,504,544 | **2,512,488** | 16,152 + 16,152 | Haar Z_673 x\| Z_24, degree 8, clusters | passed (one local run + one worker range) |
|  |  |  | 2,509,944 | 14,880 + 14,880 | Haar PSL(2,31), degree 8, clusters | passed (4 ranges) |
| (16,7) | 13, HDHDH | 4,052,108 / 4,081,072 | **4,081,410** | 29,535 + 29,535 | random, degree 11 | passed (8 ranges) |
| (17,7) | 13, HHDHHDD | 5,631,276 (beyond table) | **5,693,959** | 32,356 + 30,327 | random, degree 10 | CHECK17N |
|  |  |  | 5,693,790 | 32,356 + 30,158 | random, degree 10 | passed (8 ranges) |
| (18,7) | 13, HHDHDHDHD | 7,240,212 (beyond table) | **7,309,092** | 34,440 + 34,440 | Haar PSL(2,41), degree 9, clusters | CHECK18N |
|  |  |  | 7,290,828 | 25,308 + 25,308 | Haar PSL(2,37), degree 9 | CHECK18 |
| (19,7) | 16, HDHDH | 11,184,810 (beyond table) | 11,316,940 (candidate) | 66,065 + 66,065 | random, degree 14 | CHECK19 |
| (20,7) | 16, HHDHHDD | 15,658,734 (beyond table) | 15,795,219 (candidate) | 70,163 + 66,322 | random, degree 13 | CHECK20 |

A value counts as a result only when its all-pairs check passed (bold). The check of each graph is split into source
ranges; every range rebuilds the graph from its solution file and compares the edge-list sha256 first. The per-cell
check files (d1xD7/checks/, written by assemble_checks.py from check_results.txt) list every range with its raw output
line and state whether the ranges cover all sources. The (19,7) and (20,7) graphs were built and pass every hypothesis
the builder checks, but their all-pairs checks were not complete when the job ended (Section 7).

Unchanged, with the reason (Section 4): (7,7) 23,598, (9,7) 118,238, (10,7) 225,152, (13,7) 1,064,472 (three levels: the
hub count is the non-friendly freed set m = 81, 295, 229, 768); (11,7) 413,180 and (12,7) 693,500 (q = 9: at the cap of
Theorem 3.4). (8,7) is a Haar graph, not a hexagon construction.

How each value is obtained (Theorem 3.4 of D7_HEXAGON.md): n = (2r+1) 2N(q) + K_A + K_B, where every friendly
transition is repaired by Theorem B (R_H the spread points, a segment set; R_L+ of Proposition 1, a dual segment set),
every non-friendly one by Theorem C (the lab's mirrored sets: 768 points at q = 11, 792 at q = 13; at q = 16 the 257
points of an elliptic quadric section with sigma as in Corollary 5.3(a)), and the hubs satisfy (HG). The builder checks
all hypotheses (Computer-checked); (HG) is checked in the hub graph alone (random and PSL(2,37) graphs), with
research/d15D7b/hubfar.c from every hub in the whole graph (the (15,7) cluster graphs), or only by the all-pairs check
(the (18,7) cluster graph: its hubfar run was stopped unfinished). The type patterns are the best of all 2^L
(patterns.py, Computer-checked). Previous values: README table on master (2013 table values in D7_HEXAGON.md) and the
beyond-table values of research/frontier/beyond/BEYOND_TABLE.md (branch claude/new-cells-beyond-etos3t), which are the
plain level graphs (polygon covers) without hubs.

Edge-list sha256 (from `typed_build.py build`, equal to `make`): (14,7) 98de1d8e969ebec7e87d860ff5b242755d7bd5802cabc49527d55a7390573c62;
(15,7) 2,512,488 b1ef7d70d7ca21e35dee39f628cb50e3424b80168b1be0b404a248b7db12804d, 2,509,944
b8ee89cc3b9c9610a9ec6b9b75276e3885aeda78b2b5f588aff1a4a8f4142ac1; (16,7) 1bc34853dd30ddbd2483e5a0f90c62bd3e8acf12d5f52ee0a6950008df3c879a;
(17,7) 5,693,959 bb3c24f77d1d152916163b667d69a77a617820619762fb954fd45373601ab80f, 5,693,790
50f886bcca10c08110e48a48222e4f314d3c5427a93ed4cc62fe912097590dcd; (18,7) 7,309,092
314d5db9f3f3c4af613a56f09f93bcf149d215603adc70ba3ddb4db4deace37d, 7,290,828 b8b2137f23bc52f398774e3c528309014ae5dec368bfd8f36c56adf9524418e8;
(19,7) d71baea19994d2fb013823260b5c8f44e8407207eaa52c0b24fcc78dd1fc7fc1; (20,7) f9e6399daa20c5d1022acb10f068a19303d3ba10b38cc0c8c1e18f00d1d0dbba.
Inputs: research/p4/d6/hex/hex_q11.bin (sha256 e60db369...), hex_q13.bin (57aa5dfc...), and for q = 16 the output of
`research/d10D7/hexgen2.c 16` (hex_q16.bin, sha256 f7a701a11c2edcdc0014bd8a0eaa2a0ecce11e5953fd4bc63cc8a61c327a4394, not committed:
84 MB).

## 2. A larger dual segment set: the spread lines with nu = 0

**Proposition 1 (Theorem).** Let q be odd, or even with q >= 4, and let S, v, W, nu be as in POLISHED.md Theorem 6.5
(q odd) or Theorem 6.14 (q even): S the Hermitian spread of the hyperplane Pi, v = <e1, e6>, W the exact whisker set,
nu the function on the points of Pi off v (constant on every line of S other than v, Lemma 6.6(d) / 6.12(d)).
(a) A point X of Pi not on v lies on exactly one line of W if nu(X) != 0 and on none if nu(X) = 0.
(b) So a line n of S other than v carries a whisker at each of its q+1 points or at none, and exactly q^2 lines of S
    (the set S_0) carry none.
(c) R_L+ = L_v u W u S_0 (L_v = the lines != v meeting v) is a dual segment set of q(q^3+1) + q^2 lines.
(d) Every point of H(q) lies on a line of R_L+, so R_L+ is maximal: no line can be added.

*Proof.* (a) A whisker through X is a line l of S_z \ {v}, z = (alpha, beta) != 0, with l meeting Pi in X and
nu(X) = F(z). X lies in Pi_z iff alpha X2 + beta X5 = 0, and (X2, X5) != (0, 0) because X is in Pi and not on v
(Lemma 6.1(d)), so these z form a punctured line {t z0 : t != 0} of F^2. For each of them there is exactly one line of
S_z through X (Lemma 6.1(b)); it is not v, it is not in S (6.1(e)), so it meets Pi only in X (6.1(c)), and different z
give different lines (6.1(e)). G is a homogeneous cubic and the norm a^2 + c b^2 (resp. a^2 + ab + delta b^2) a
homogeneous anisotropic quadratic form, so F(t z0) = t F(z0) with F(z0) != 0 (G has no zero). Hence F takes every
nonzero value exactly once on the punctured line and never 0: one whisker through X if nu(X) != 0, none if nu(X) = 0.
(b) nu is constant on n. Counting whiskers by their point in Pi: |W| = q^2(q^2 - 1) = (q+1) #{n : nu(n) != 0}, so
q^2(q-1) lines carry whiskers and q^3 - q^2(q-1) = q^2 do not.
(c) A line n of S_0 meets no other line of R_L+: other lines of S are opposite n; a line of L_v has its points at
distance <= 3 from v, while the points of n are at distance 5; a whisker meets Pi in a point with nu != 0 by (a). So n
is an isolated line of R_L+, and R_L+ minus S_0 is the dual segment set of CONICS.md Lemma 3.1.
(d) Points at distance <= 3 from v lie on lines of L_v; free points on whiskers (W is exact); points of Pi off v on a
whisker or on a line of S_0 by (a), (b). A line outside R_L+ would therefore meet lines of R_L+ in all its q+1 points.
[]

*Computer-checked.* typed_build.py computes S, W and S_0 from the coordinates and asserts (a)-(c) (nu constant on every
spread line, |S_0| = q^2, whisker counts 0 or 1, the dual segment property) for q = 4, 5, 7, 11, 13, 16. The squad
(card c7) found the q^2 "zero-carry" spread lines first, by computer, at q = 4, 5, 7.

**Consequence.** In every typed layout where the smallest slot count is R_L + (non-friendly elements), the hub count
rises by q^2 per side: (14,7) +242, (16,7) +338, (17,7) +169 (one side), (19,7) +512, (20,7) +256 (one side).

## 3. Is the exact whisker set the largest dual segment set compatible with R_H?

- **Theorem (restatement).** Theorem B treats each friendly transition on its own, so any dual segment set may be used on
  the D -> H transitions together with R_H (the spread points, the largest segment set, D7_HEXAGON.md Proposition 1.4) on
  the H -> D ones. The bound for dual segment sets is (q+1)(q^3+1), reached only by the pencils of an ovoid, which H(q)
  does not have for q prime >= 5 or q even.
- **Theorem (Proposition 1).** No: the whisker set plus the lines meeting v is not maximal; adding the q^2 spread lines
  with nu = 0 gives q(q^3+1) + q^2, and that set is maximal. Its gap to the bound is q^3 - q^2 + 1.
- **Computer-checked (squad round conics2-r1).** It is not maximum in general: the largest dual segment set of H(2) has
  exactly 25 lines (card c6, SAT: 25 found, 26 unsatisfiable; card c7, MaxSAT: 25), against q(q^3+1) + q^2 = 22 and the
  bound 27; H(4) has a dual segment set of 288 lines (card c8, simulated annealing; 68 centres, 16 full pencils and 52
  pencils of 4 lines, no isolated line), against 276 and the bound 325. All sets re-checked with
  research/squads/conics2-r1/tools/dualseg_check.py. At q = 5 and 7, local search from R_L+ (2.9 million moves at q = 5)
  found nothing larger; the annealer of card c8 reached only 508 at q = 5. At q = 3 the ovoid pencils give the bound 112.
- **Heuristic.** The q = 4 set suggests that large dual segment sets prefer many nearly full pencils (centres) to
  isolated lines; whether a pencil-type construction beats q(q^3+1) + q^2 for q >= 11 is open.

## 4. Can the non-friendly transitions free more than the mirrored 768 / 792-point surgery?

- **Theorem (restatement, D7_HEXAGON.md Sections 4-6).** With three levels (r = 1) every level has one outgoing
  transition and some transition is non-friendly, so the hub count is at most the non-friendly freed set: (7,7), (9,7),
  (10,7) and (13,7) move only with a larger m (81, 295, 229, 768). At q = 9 (the H(9) cells (11,7) and (12,7)) every
  transition is a duality transition and frees the point set of the Hermitian spread, the largest segment set (7,300 =
  (q+1)(q^3+1), Proposition 1.4; since H(9) has ovoids, a dual segment set can reach the same size), so 413,180 and
  693,500 are the cap of Theorem 3.4 (D7_HEXAGON.md Corollary 8.2) and whiskers cannot raise them.
- **Computer-checked, negative.** At q = 5 (the (7,7) record, 81 freed points) four independent approaches found no
  repaired non-friendly transition with 82 freed points: a mirrored-set search (card c1: no extra mirrored pair matches
  the record's types; tabu partial ovoids reach only 56 of the record's 72), simulated annealing on sigma maximizing the
  number of points where sigma is a local duality (card c2: never above 81, and the set of such points under the record
  sigma is exactly R), local search adding one point and repairing sigma by swaps (card c3: the best state still has 589
  pairs beyond distance 7, of which 317 come from the new point itself), SAT at q = 3 (card c5, too large without
  symmetry breaking), and the whole three-level (7,7) graph with hubs instead of one transition (card c4: freeing an
  82nd point breaks 864 to 1,188 ordered pairs over 12 choices of the point, all between level vertices, none involving
  a hub, so neither the third level nor the hubs repair them; local search on sigma brought one case to 744). The scorer (tools/transcheck.py) is an exact bitset BFS of the two-level graph, validated on the
  record (0 bad pairs) and on negative controls (one more freed point: 612 to 697 bad pairs).
- **Heuristic.** A freed point x needs sigma to map the q(q+1) points collinear with x to lines whose radius-3 balls
  cover the points of the next level (Theorem C makes this exact with the lines concurrent with sigma(x)); the
  experiments show no slack for an 82nd point at q = 5. A larger m seems to need a structurally new sigma (for example
  a partial duality on a large substructure), not local changes.

## 5. Cluster-assisted Haar hub graphs

**Lemma 2 (Theorem).** Index the hubs of both sides by a group G, join line-side hub x to point-side hubs x s (s in S),
and suppose that in some H-level the line-side hubs of every left coset x H_j take free slots at points of one line of
H(q) (in some D-level the point-side hubs of every coset y K_j likewise). Then two line-side hubs x, x w are within
distance 6 when w lies in (S S^-1)^k (k <= 3), in C_A = U H_j, in C_A S S^-1, in S S^-1 C_A, or in S C_B S^-1 (C_B =
U K_j); dually on the point side with S^-1 S, C_B and S^-1 C_A S. *Proof.* Two hubs on points of one line are joined by
hub - point - line - point - hub (length 4, or 2 on the same point); the Haar steps have length 1. []

*Computer-checked.* clhub.py searches S and cyclic subgroups until the union covers G on both sides; typed_build.py
places each coset on one spread line (the free slots there are spread points, 12 or 24 per line at q = 11, 28 or 42 at
q = 13). (15,7): G = PSL(2,31) (14,880), |S| = 8, subgroups of orders 16, 15 (line side) and 15, 16, 15 (point side);
the hub graph alone leaves 89,280 same-side pairs beyond 6, all joined through the clusters: research/d15D7b/hubfar.c
from all 29,760 hubs gives far_pairs=0, max_ecc=7 (d15D7/checks/hubfar.txt). This is the PSL(2,31) graph that the
plain search of job "conics" missed by one element. (15,7), larger: G = Z_673 x| Z_24 (16,152; clhub2.py), |S| = 8,
subgroups of order 24 (two line-side and three point-side cluster levels); hubfar from all 32,304 hubs gives
far_pairs=0, max_ecc=7 (d15D7/checks/hubfar_meta.txt). (18,7): G = PSL(2,41) (34,440), |S| = 9, subgroups of orders
10, 21, 20, 20, 21 (line side) and 21, 10, 21, 21 (point side); the hub graph alone leaves 654,360 same-side pairs
beyond 6, all to be joined through the clusters (hubfar from all 68,880 hubs was stopped unfinished after an hour; the all-pairs check covers it). PSL(2,43) (39,732 hubs) did not cover: the search stopped with 2 and 6 elements missing
(d18D7/clhub_psl43.log).

## 6. Files

- typed_build.py: the builder (any number of levels, any type string; q = 11, 13 from research/p4/d6/hex/hex_q*.bin,
  q = 16 from research/d10D7/hexgen2.c output; --nu0 adds S_0; hub graphs random with batched 2-switch repair, explicit,
  or cluster-assisted). `make HEXBIN TYPES NONFRIENDLY HUBS OUT.sol OUT.edges [--nu0]` and `build HEXBIN SOL OUT.edges`.
  It reproduces the checked (16,7) edge list of job "conics" byte for byte (sha256 350f9e07...) from that job's hub graph.
- patterns.py: exhaustive search of type patterns (slot counts).
- psl_hub.py, clhub.py: Haar and cluster-assisted Haar hub graphs; ovoid_greedy.py, elliptic_even.py: the q = 16
  non-friendly set (257 points of an elliptic quadric section Q^-(3,16); greedy found only 177).
- d1xD7/: build logs, hub graph files, checks. check_sessions.txt: the remote check workers and their source ranges;
  check_results.txt: their result lines, copied from the raw tool output.
- Solutions: research/frontier/sols/d1xD7_hex*_typedwhisk*.sol (each names its inputs by sha256).
- Squad round: research/squads/conics2-r1/ (brief, scorers, data, cards, scoreboard); research/squads/LOG.md.
