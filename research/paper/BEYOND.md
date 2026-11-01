---
title: "Beyond the 2013 table: first values for 64 cells of the bipartite degree–diameter problem"
author: "Doğa Özden, with Claude Code (lab notes, job paper-beyond)"
date: "November 1, 2026 (draft)"
---

# 1. What this note covers

N^b^(Δ, D) is the largest number of vertices of a bipartite graph with maximum degree Δ and diameter at most D.
The 2013 survey table (Miller–Širáň, DS14v2, as reproduced on the Combinatorics Wiki) lists lower bounds for
Δ ≤ 16 and D ≤ 10. Between October 26 and November 1, 2026, cloud jobs of the lab built and checked graphs for cells
outside that table. This note gives one value for each of 64 of them:

- Δ = 17, 18, 19, 20 at D = 5, …, 10 (24 cells);
- D = 11 at Δ = 3, …, 16 and D = 12 at Δ = 3, …, 14 (26 cells);
- D = 13 at Δ = 3, …, 10 and D = 14 at Δ = 3, …, 8 (14 cells).

The Δ = 17..20 cells at D = 3 and 4 were filled in the same week but are not in the table below: at Δ = 17, 18, 20
they are incidence graphs of PG(2, Δ−1) and W(Δ−1) (Moore graphs, so optimal), and at Δ = 19 they are the lab's
fourth-hat graph (624) and the AS(17) graph of Corollary A1 (10,982), both checked all-pairs by the coordinator on
October 26.

Each value is a lower bound: one explicit graph, built from files in the repository. All but three were checked
exactly by a program that does not share code with the search that found them; the three level graphs at D = 7 rest
on a theorem (section 4). A literature card of the new-cells-beyond job (`research/squads/beyond/r2/d10/LIT.md` on its
branch) looked for published bipartite values in 48 of these cells (Δ = 17..20 at D ≤ 10, and D = 11, 12 at
Δ ≤ 10) and found none, but it could not read the Combinatorics Wiki page (HTTP 503) or the tables of some papers. For
the other cells no search was made. So we call the values *first values for the lab*, not records. For cubic graphs in
particular, published censuses may contain larger bipartite graphs of these diameters; this has not been checked.

For comparison, the bipartite Moore bound is M~b~(Δ, D) = 2(1 + (Δ−1) + … + (Δ−1)^D−1^), and for 5 ≤ D ≤ 187,
D ≠ 6, N^b^(Δ, D) ≤ M~b~(Δ, D) − 6 (Feria-Purón and Pineda-Villavicencio, Discrete Appl. Math. 160 (2012),
Prop. 6.4). Our values are 100 % of the Moore bound at (17,6), (18,6), (20,6), 80 % at (19,6), 24–27 % at D = 5,
14–16 % at D = 7, 4.5–7.7 % for the orbit-S Haar graphs at D = 8..14 (0.8–3.1 % in the four cells stopped at the
jobs' size cap), and 7–36 % for the metacyclic Haar graphs and lifts at Δ = 3..6.

# 2. Where the numbers come from

Every value in the table was copied from one of these, and the vertex counts were re-derived from the group orders
or formulas (`python3 research/paper/make_beyond.py` prints the comparison):

| job (dates) | branch | cells |
|:-----------------------|:--------------------------------------|:---------------------------------------------------|
| new-cells-beyond (Oct 26–31) | claude/new-cells-beyond-etos3t | Δ = 17..20 at D = 3..10; first values at D = 11, 12 for Δ = 3..10 |
| conics-2 (Oct 29–30) | claude/conics-2-diameter-7-ic0oat | (17,7) |
| own-small (Oct 26–30) | claude/own-small-cells-dkwo42 | (3,12) |
| beyond-d11 (Oct 31–Nov 1) | claude/new-cells-d11-d12-beyond-8sas9r | D = 11 at Δ = 11..14, D = 12 at Δ = 11..13; raises at Δ = 4..10 |
| beyond-d11b (Nov 1) | claude/beyond-d11-d12-new-cells-3t3djx | (15,11), (16,11), (14,12); raises of (12,12), (13,12) and of Δ = 4..6 |
| beyond-d13 (Nov 1) | claude/beyond-d13-search-z35z61 | D = 13 at Δ = 3..10, D = 14 at Δ = 3..8 |
| beyond-small (Nov 1) | claude/beyond-small-cells-fwb6si | (17,5); exact checks at D = 6 |

On master the values live in `research/RESULTS.md` (harvest and coordinator lines), the harvest check reports
`research/frontier/runs/harvest_check_2026-10-31.txt` and `…_2026-11-01.txt`, and the coordinator's logs
`research/coordinator_check/check_2026-10-29.txt` … `check_2026-11-01.txt`. On the branches they are in
`research/frontier/beyond/BEYOND_TABLE.md` (each branch has its own version), `research/frontier/beyond/BEYOND_SMALL.md`
(beyond-small), `research/frontier/beyond13/` (beyond-d13) and `research/frontier/beyond11/` (beyond-d11). Master has
no BEYOND_TABLE.md yet. Where the branches and master disagree, the table takes the largest value that has a check of
its own, and says where it is. Three such cases: (17,5), where master has 35,618 and beyond-small has 35,728; (3,11),
where master has 1,344 (a voltage lift from own-small) and every BEYOND_TABLE.md has 1,474; and (4,11), (5,11),
(6,11), (4,12), (5,12), which the beyond-d13 and beyond-d11b branches raised in parallel; master holds the larger value
of each pair.

# 3. The table

**Columns.** *construction*: "Haar, orbit S" is a Haar graph H(G, S) with S a union of orbits of a group
automorphism (section 5.1); "Haar, random S" has S searched with no imposed symmetry (section 5.2); "(size cap)"
marks the four cells where the job stopped at its size limit with the first S that worked. *Group or base graph*:
Z~m~ ⋊~r~ Z~k~ is the group of pairs (a, j), a mod m, j mod k, with (a, j)(b, l) = (a + r^j^ b, j + l); "Frobenius"
means m is prime and r has order k mod m. *Check* (a semicolon separates checks run at different times; "+" joins two
independent checkers in one report):

- gen = `research/frontier/haarcheck_gen.c`; sl = `research/frontier/haarcheck_sl.c`; psl =
  `research/structured/tools/haarcheck_psl.c` (the reference checkers); h2 = `research/frontier/haarcheck2.c`;
  ind = `research/frontier/check_haar_indep.py`; bh2 = `research/frontier/build_haar2.py`; mc =
  `research/frontier/beyond13/metacheck.py` or `metacheck2.py` (beyond-d13 branch). All of these build the group from
  its definition and run a BFS from (e,A) and from (e,B); see section 4.
- apsp = all-pairs BFS with no symmetry assumed (`research/lifts/coordinator_check/apsp.c`, or its multithreaded
  versions apsp_mt / apsp_fast); "coord." = run by the coordinator on the Mac mini; "8 ranges" = the source vertices
  split over eight cloud workers.
- auto = exact BFS from one vertex per orbit of an automorphism group that the checker verifies itself
  (`research/frontier/beyond/hex6/apsp_auto.c`, beyond-small branch).
- samp = BFS from 64 random vertices only (not a proof); "theorem" = the diameter bound is a theorem for every
  choice in the construction.
- † = run by this job; logs in `research/paper/beyond_checks/`.

*Where*: "master" = harvested or recorded by the coordinator on master; "branch" = only on the job's branch.
Footnotes: ᵃ master has 35,618 (coordinator apsp, October 31). ᵇ no exact check (section 4). ᶜ master has 1,344.
ᵈ one checker so far; the reference check, split into two halves as for the other cells above 20 billion vertices,
has not been run.

<!-- TABLE -->
| (Δ, D) | value | construction | group or base graph | check | where |
|:-------|--------------:|:---------------------------|:-----------------------------------|:-----------------------|:-----------|
| (17, 5) | 35,728 | route-chart lift + 1,936 hubs (88 Z₂₂-orbits) | (16,5) graph: K₃,₃ + doubled matching, Z₂₂, fibre F₄⁴ | apsp, bfs_all; apsp† | branch ᵃ |
| (18, 5) | 47,600 | multi-doubled-matching lift | W(13); 2 doubled matchings; Z₂ × Z₅ | apsp; coord. apsp | master |
| (19, 5) | 52,428 | doubled-matching lift | W(16); Z₆ | apsp; coord. apsp | master |
| (20, 5) | 75,000 | route-chart lift over F₅ | K₃,₃ + doubled matching, Z₂₀, fibre F₅⁴ | apsp; coord. apsp | master |
| (17, 6) | 2,236,962 | Moore graph | H(16) | classical; auto | branch |
| (18, 6) | 3,017,196 | Moore graph | H(17) | classical; auto | branch |
| (19, 6) | 3,203,968 | Theorem D, q = 17, m = 2 | H(17) doubled with levels and whiskers | theorem (Lean); auto | branch |
| (20, 6) | 5,227,320 | Moore graph | H(19) | classical; auto | branch |
| (17, 7) | 5,693,959 | typed whisker cover + hubs | H(13); 32,356 + 30,327 hubs | coord. apsp; apsp (8 ranges) | master |
| (18, 7) | 7,240,212 | level graph | 9 copies of H(13), 4 matchings, Z₉ | theorem; samp | branch ᵇ |
| (19, 7) | 11,184,810 | level graph | 5 copies of H(16), 2 matchings, Z₅ | theorem; samp | branch ᵇ |
| (20, 7) | 15,658,734 | level graph | 7 copies of H(16), 3 matchings, Z₇ | theorem; samp | branch ᵇ |
| (17, 8) | 41,373,072 | Haar, orbit S | SL(2,53) × Z₁₃₉ | sl + h2 | master |
| (18, 8) | 57,637,680 | Haar, orbit S | SL(2,61) × Z₁₂₇ | sl + h2 | master |
| (19, 8) | 86,317,296 | Haar, orbit S | PSL(2,103) × Z₇₉ | psl + ind | master |
| (20, 8) | 122,739,120 | Haar, orbit S | PSL(2,71) × Z₃₄₃ | psl + ind | master |
| (17, 9) | 501,707,400 | Haar, orbit S | PSL(2,101) × Z₄₈₇ | psl + ind | master |
| (18, 9) | 790,626,816 | Haar, orbit S | SL(2,127) × Z₁₉₃ | sl + h2 | master |
| (19, 9) | 1,218,394,320 | Haar, orbit S | SL(2,131) × Z₂₇₁ | sl + h2 | master |
| (20, 9) | 1,823,175,864 | Haar, orbit S | PSL(2,163) × Z₄₂₁ | psl + gen | master |
| (17, 10) | 7,022,052,336 | Haar, orbit S | PSL(2,313) × Z₂₂₉ | psl + gen | master |
| (18, 10) | 11,787,972,672 | Haar, orbit S | PSL(2,223) × Z₁₀₆₃ | psl + gen | master |
| (19, 10) | 19,233,722,496 | Haar, orbit S | SL(2,607) × Z₄₃ | sl + gen | master |
| (20, 10) | 30,518,778,360 | Haar, orbit S | PSL(2,421) × Z₄₀₉ | psl (2 halves) + gen | master |
| (3, 11) | 1,474 | Haar, all pairs {x, y} searched | Z₆₇ ⋊₉ Z₁₁ | apsp; apsp† | branch ᶜ |
| (4, 11) | 30,334 | Haar, random S | Z₅₂₃ ⋊₉ Z₂₉ (Frobenius) | bh2 + apsp | master |
| (5, 11) | 311,426 | Haar, random S | Z₅₀₂₃ ⋊₂₈₈₆ Z₃₁ (Frobenius) | bh2 + apsp | master |
| (6, 11) | 2,122,518 | Haar, random S | Z₂₀₈₀₉ ⋊₁₂₉₇₂ Z₅₁ (Frobenius) | bh2; mc† | master |
| (7, 11) | 11,012,976 | Haar, orbit S | SL(2,53) × Z₃₇ | gen + sl | master |
| (8, 11) | 45,329,808 | Haar, orbit S | SL(2,283) | gen + sl | master |
| (9, 11) | 155,250,816 | Haar, orbit S | SL(2,223) × Z₇ | gen + sl | master |
| (10, 11) | 460,691,568 | Haar, orbit S | SL(2,613) | gen + sl | master |
| (11, 11) | 1,241,299,248 | Haar, orbit S | SL(2,853) | gen + sl | master |
| (12, 11) | 2,976,066,240 | Haar, orbit S | SL(2,239) × Z₁₀₉ | gen + sl | master |
| (13, 11) | 6,781,213,392 | Haar, orbit S | SL(2,563) × Z₁₉ | gen + sl | master |
| (14, 11) | 14,381,398,080 | Haar, orbit S | SL(2,1009) × Z₇ | gen + sl | master |
| (15, 11) | 28,655,908,512 | Haar, orbit S | SL(2,617) × Z₆₁ | gen + sl (2 halves) | master |
| (16, 11) | 29,961,590,400 | Haar, orbit S (size cap) | PSL(2,449) × Z₃₃₁ | gen only | branch ᵈ |
| (3, 12) | 2,368 | voltage lift | cubic 4 + 4-vertex base; Z₃₇ ⋊ Z₈ = SmallGroup(296,3) | coord. rebuild + apsp | master |
| (4, 12) | 74,066 | Haar, random S | Z₁₂₇₇ ⋊₉₆₄ Z₂₉ | apsp + mc; coord. apsp | master |
| (5, 12) | 1,058,342 | Haar, random S | Z₈₉₆₉ ⋊₂₀₅ Z₅₉ (Frobenius) | bh2; mc† | master |
| (6, 12) | 9,366,240 | Haar, orbit S | PSL(2,79) × Z₁₉ | gen + psl | master |
| (7, 12) | 59,838,504 | Haar, orbit S | PSL(2,67) × Z₁₉₉ | gen + psl | master |
| (8, 12) | 284,095,056 | Haar, orbit S | PSL(2,167) × Z₆₁ | gen + psl | master |
| (9, 12) | 1,105,785,120 | Haar, orbit S | PSL(2,241) × Z₇₉ | gen + psl | master |
| (10, 12) | 3,712,424,352 | Haar, orbit S | PSL(2,337) × Z₉₇ | gen + psl | master |
| (11, 12) | 11,189,148,096 | Haar, orbit S | PSL(2,223) × Z₁₀₀₉ | gen + psl | master |
| (12, 12) | 29,996,171,040 | Haar, orbit S | PSL(2,241) × Z₂₁₄₃ | gen + psl (2 halves) | master |
| (13, 12) | 29,997,644,040 | Haar, orbit S (size cap) | PSL(2,181) × Z₅₀₅₉ | gen + psl (2 halves) | master |
| (14, 12) | 29,996,171,040 | Haar, orbit S (size cap) | PSL(2,241) × Z₂₁₄₃ | gen + psl (2 halves) | master |
| (3, 13) | 3,400 | cyclic voltage lift | Desargues graph GP(10,3); Z₁₇₀ | apsp; coord. apsp | master |
| (4, 13) | 192,382 | Haar, random S | Z₂₂₃₇ ⋊₁₉₈₄ Z₄₃ (Frobenius) | apsp + mc; coord. apsp | master |
| (5, 13) | 3,594,910 | Haar, random S | (Z₁₁ ⋊₄ Z₅) × (Z₂₉₇₁ ⋊₁₇₆₄ Z₁₁) | mc; bh2† | branch |
| (6, 13) | 41,734,392 | Haar, orbit S | PSL(2,83) × Z₇₃ | gen; psl† | branch |
| (7, 13) | 312,227,760 | Haar, orbit S | SL(2,229) × Z₁₃ | gen; sl† | branch |
| (8, 13) | 1,739,514,000 | Haar, orbit S | SL(2,499) × Z₇ | gen; sl† | branch |
| (9, 13) | 7,924,036,032 | Haar, orbit S | SL(2,593) × Z₁₉ | gen; sl† | branch |
| (10, 13) | 19,980,294,768 | Haar, orbit S (size cap) | PSL(2,503) × Z₁₅₇ | gen only | branch ᵈ |
| (3, 14) | 5,706 | cyclic voltage lift | Pappus graph; Z₃₁₇ | apsp; coord. apsp | master |
| (4, 14) | 497,042 | Haar, random S | Z₂₇₃₁ ⋊₂₄₀₀ Z₉₁ | apsp + mc; coord. apsp | master |
| (5, 14) | 12,795,166 | Haar, random S | Z₁₄₈₇₈₁ ⋊₈₅₁₇₅ Z₄₃ | mc; bh2† | branch |
| (6, 14) | 187,990,656 | Haar, orbit S | SL(2,97) × Z₁₀₃ | gen; sl† | branch |
| (7, 14) | 1,674,490,944 | Haar, orbit S | PSL(2,223) × Z₁₅₁ | gen; psl† | branch |
| (8, 14) | 11,325,238,056 | Haar, orbit S | PSL(2,397) × Z₁₈₁ | gen; psl† | branch |
<!-- /TABLE -->

Counts: 44 of the 64 values are on master, each with two independent checkers or an all-pairs BFS: 24 at D = 11, 12,
the 12 Haar graphs at Δ = 17..20 and D = 8..10, 4 at D = 13, 14 with Δ = 3, 4, and (18,5), (19,5), (20,5), (17,7).
For two of them, (6,11) and (5,12), the second checker was run by this job. 20 are on branches only: 10 at D = 13, 14
with Δ = 5..10 (nine now with two checkers, the second one run by this job; (10,13) with one), (16,11) (one checker),
the four D = 6 values (exact check via automorphisms), the three level graphs at D = 7 (theorem plus sampled BFS), and
two values above master's, (17,5) and (3,11), each checked all-pairs twice.

# 4. How the values were checked

**Haar graphs.** H(G, S) has vertices (g, A) and (g, B) for g in G and edges (g, A) ~ (sg, B) for s in S. Right
multiplication by any h in G maps edges to edges and acts transitively on each side, so every vertex of one side has
the same eccentricity, and the diameter is the larger of the eccentricities of (e, A) and (e, B). Two BFS therefore
decide the diameter exactly. Both are needed: for odd D and non-abelian G one side can pass while the other fails
(the first odd-D version of the new-cells-beyond search counted one side only; the checkers, which run both BFS,
rejected a (10,11) candidate it produced, and the file was discarded). Every checker listed above builds the group from its definition (matrices mod p, or pairs
(a, j) with the semidirect product rule), checks that the Δ generators are distinct, and runs both BFS. The reference
checkers sl and psl were written separately from gen, with their own element indexing; above about 20 billion
vertices their two BFS are run as two jobs ("2 halves"), which is the same check split in two. bh2 can also write
the edge list, so small Haar graphs can be given to apsp as well.

**Edge lists.** The non-Haar graphs (lifts, hub graphs, the level graphs at small q) were checked by apsp, which reads
an edge list and runs a BFS from every vertex (64 sources at a time) with no symmetry assumed; it also checks
simplicity, the maximum degree and bipartiteness. By the lab's convention each graph is also run at diameter D − 1,
where it must fail.

**D = 6 (Moore graphs and Theorem D).** These have 2.2–5.2 million vertices; an all-pairs BFS is out of reach on the
4-core cloud machines. The beyond-small job checked them exactly with apsp_auto: it is given permutations of the
vertex set, verifies that each maps every edge to an edge, and runs a BFS from one vertex per orbit of the group they
generate (eccentricity is constant on orbits). For H(q) the permutations come from diagonal matrices that preserve
the quadric and Tits' line equations (10,026 to 16,230 orbit representatives); for Theorem D at q = 17 one generator
of order 16, with 200,486 orbit representatives. apsp_auto agrees with apsp on H(4) and on the
Theorem D graphs at q = 5 and 7, and fails at D − 1. The H(q) values are also classical (Tits), and Theorem D is proved
in Lean for every odd q.

**D = 7 level graphs.** (18,7), (19,7), (20,7) are 2r + 1 copies of a generalized hexagon joined by r matchings. Their
diameter is at most 7 for every choice of matchings (research/synthetic/SYNTHETIC.md, Theorem 4.2), and the builder
was checked all-pairs at q = 3, 4 for r = 1..3. The instances themselves (7.2–15.7 million vertices) only had a BFS
from 64 random vertices, which found eccentricity 7. That is a sanity check of the builder, not a check of the graph;
the value rests on the theorem. No exact check (all-pairs or by automorphisms) has been run for these three graphs.

**Second checks run by this job.** Where a row had only the search session's checker, this job ran a different one
on the same file (sha256 in each log): sl or psl on (6,13), (7,13), (8,13), (9,13), (6,14), (7,14), (8,14); bh2 on
(5,13) and (5,14); mc on master's (5,12) and (6,11), which had been checked by bh2 only (by the session and again by
the harvest); and apsp on the 1,474-vertex (3,11) graph and the 35,728-vertex (17,5) graph. All of them reported
VALID. (16,11) (29,961,590,400 vertices) and (10,13) (19,980,294,768) need about 11 GB and 7 GB for each half of the
reference check and several hours per half single-threaded; they were not run here.

# 5. Methods

## 5.1 Haar graphs with orbit-closed generator sets (Δ ≥ 6 at D = 8..14)

**Why Haar graphs, and how big.** For a Haar graph the diameter condition is a covering condition in G: every element
must be reached by a word of length at most D − 1 in S and S^−1^ (alternating). About W = Δ(Δ − 1)^D−2^ such words
exist. If they behaved like random elements, the expected number of elements missed would be μ = N e^−W/N^ with
N = |G| (research/frontier/SIZE_LAW.md). Annealing closes the last holes only when μ is small (SIZE_LAW.md measured
a limit μ\* of about 9–40, depending on effort), so the jobs chose group orders by this "size law". The Δ = 17..20
values were taken at μ ≈ 3–13 and not pushed further; the D = 11..14 values with orbit S sit at μ ≈ 5–14 (the
branch tables give μ for each row); the four cells at the size cap have μ ≈ 0.

**Groups.** G = SL(2, p) × Z~n~ or PSL(2, p) × Z~n~, p prime. These have many orders near any target, cheap
arithmetic, and an automorphism α of order 3: conjugation by a matrix of order 3 on the first factor, times z ↦ rz
with r of order 3 mod n on the second.

**Orbit search.** S = {e} ∪ F ∪ (orbits of α of size 3), with F a few α-fixed elements. Making S α-invariant shrinks
the search space and makes the whole word set α-invariant; in the lab's earlier runs at D = 7..10 this broke the wall
where random S stops working (README, research/structured/, research/theory/). The search anneals the orbit
representatives; the
cost is the number of uncovered elements, counted by a bit-parallel BFS (`research/bighaar/haar_big.c` and the
beyond-d11 version `research/frontier/beyond11/haar_big0.c`, 64-bit indices, N/2 bytes of memory, so 10^10^-element
groups fit in about 5 GB). beyond-d11 added two things: S made of free orbits only, without e (right for 3 | Δ), and a
fix in the choice of the automorphism for orbit sizes 4, 6 and 10 (the old code could pick a matrix of order 2 or 3
there; orbits of size 3 and 5 were not affected, so no earlier result changed).

**Odd D is harder than even D.** For D = 2h + 1 the diameter condition is (S^−1^S)^h^ = G and (SS^−1^)^h^ = G. The
beyond-d11 job proved (research/frontier/beyond11/ODD_D_HOLES.md, on its branch) that the words reaching an
involution come in pairs (reverse and invert), and the words reaching a central element are closed under rotation by
two letters, and a central hole is a hole on both sides at once. In the random model an involution is then missed with
probability about e^−λ/2^ and a central element about e^−λ/h^, against e^−λ^ for an ordinary element (λ = W/N).
PSL(2, p) has about p²/2 involutions, SL(2, p) only −I, and G × Z~n~ has n or 2n central elements. The rule that came
out of this, and that gave most D = 11 and 13 values: at odd D use SL(2, p) × Z~n~ with small n (n ≤ 61 at D = 11,
except (12,11), which was found before the rule); at even D, PSL(2, p) × Z~n~ with moderate or large n is fine. PSL with n = 1 is the worst choice at odd D (every one of
the about 130 holes of a random S was an involution) although it works at even D. Measured hole counts of random S
agreed with these rates within a factor 1.3–2.

**Size caps.** The jobs set a size limit so that the low-memory checkers finish in hours: 20 billion vertices for
beyond-d11 and beyond-d13, 30 billion for beyond-d11b. In (16,11), (13,12), (14,12) and (10,13) the first S tried
worked at the cap, so these values are limits of checking time, not of the search. (12,12) and (15,11) are also close
to the cap, but there the search had to work: μ ≈ 12 and 45 evaluations, μ ≈ 5 and 13 evaluations.

## 5.2 Metacyclic Haar graphs (Δ = 3..6 at D = 11..14)

At small Δ the groups are small (10^3^ to 10^7^ elements) and other groups can be tried. Two kinds won.

**Odd-order and Frobenius groups.** In Z~m~ ⋊~r~ Z~k~ with m prime and r of order k > 1 mod m, the centre is trivial,
and if mk is odd there are no involutions (beyond-d13, research/frontier/beyond13/THEORY.md, Fact 1, with a two-line
proof). So the special holes of section 5.1 do not exist, and only the ordinary ones are left. This is what beat the
SL/PSL values at odd D: (4,13) 192,382 against 170,520 for the best PSL(2,29) × Z~7~ orbit graph, (5,13) 3,594,910
against 3,217,056, and (4,11) 30,334 against 24,360. Products of two such groups also work ((5,13)).

**Random S instead of orbits.** At Δ = 4 the orbit form {e, x, αx, α²x} has one free element, and at Δ = 5 one fixed
generator plus one orbit; a random S has Δ − 1 free elements. This is why the metacyclic groups with random S also won
the even-D cells at Δ = 4, 5, by 1–8 %. The search is plain annealing of S (`research/frontier/haar_gen3.c`, and
the beyond-d11b versions with save/resume and a targeted finisher, `research/squads/beyond11b/tools/`; beyond-d13's
bit-parallel `research/frontier/beyond13/meta/hmeta.c`), plus scans of every metacyclic group in an order range with
short runs on each.

**Not too abelian.** Z~m~ ⋊~r~ Z~k~ has an abelian subgroup of index k, and for small k words collide. Measured at
(4,13) with random S (squad card r2/e11 of beyond-d13): the words of length 12 from (e, A) reach 1 % of G for k = 1,
6 % for k = 3, 73 % for k = 5, 91 % for k = 9 and 97–99 % for k ≥ 11. The Δ = 4, 5, 6 values in the table use single
groups with k = 29 to 91, or (at (5,13)) a product of two groups with k = 5 and k = 11.

**Cubic cells.** At Δ = 3 with S = {e, x, y} all pairs (x, y) can be searched in each group, in 0.1–2 s per group.
The new-cells-beyond job swept every metacyclic group of order 541–1,100 at D = 11 (641 groups, one r of each order
per m) and found Z~67~ ⋊~9~ Z~11~ (1,474 vertices), the only metacyclic hit in that range. At D = 12 the best
metacyclic Haar graph (2,176, Z~68~ ⋊~3~ Z~16~) is below the own-small job's voltage lift over Z~37~ ⋊ Z~8~ (2,368),
which the table lists.

The metacyclic idea reached Δ = 6 only at D = 11; at (6,12), (6,13) and Δ = 7 it stopped at 2 to 14 uncovered
elements, and SL/PSL orbit graphs stayed ahead.

## 5.3 Cyclic voltage lifts (Δ = 3 at D = 13, 14)

Take a small cubic bipartite base graph B and a voltage x~e~ in Z~n~ on each edge; the lift has vertices (v, g) and
edges (u, g) ~ (w, g + x~e~). Rotation g ↦ g + c is an automorphism, so only BFS from the base vertices (with g = 0)
are needed. The beyond-d13 job annealed the voltages (`research/frontier/beyond13/lifts/lift.c`, from squad card
r2/e16; for short runs the cooling has to be spread over about 1,000 evaluations, not the default 20,000) and then
ran an exhaustive search over single-voltage changes with a tabu list (`lifts/scan_h02.c`, from card r5/h02). Results:
the Desargues graph GP(10,3) over Z~170~ at D = 13 (3,400 vertices) and the Pappus graph over Z~317~ at D = 14 (5,706).
Both beat every Haar graph tried at those cells (2,880 for A~6~ × Z~4~ at D = 13, all pairs searched; 5,040 for
PSL(2,7) × Z~15~ at D = 14).

*An upper bound for this method* (THEORY.md, Fact 2). The lift of a walk from (s, 0) ends at (v, Σ c~e~ x~e~),
where c is the walk's net traversal vector (signed edge counts). So if the lift has diameter ≤ D, then n is at most
the number of distinct net traversal vectors of walks from s to v of length ≤ D, for every pair s, v. For GP(10,3)
this allows n ≤ 647 at D = 13 and n ≤ 1,197 at D = 14; the lifts found have n = 170 and (for GP(10,3) at D = 14) 282.
At D = 11, 12 the lifts did not beat the metacyclic values, and at Δ = 4, 5 lifts of K~4,4~, PG(2,3), GQ(3,3) and
random bases stayed below the Haar values.

## 5.4 Route-chart lift plus hubs: (17,5)

(17,5) was the one cell in this note where none of the lab's formula families applies: the multi-doubled-matching
lifts need Δ = q + 1 + (an even number), and route charts need Δ = (letters) × (field size); 17 is neither for a
usable prime power q. The new-cells-beyond job left only the floor 33,792, the (16,5) graph itself. The beyond-small
job added vertices to that graph.

**Base.** The (16,5) graph (`research/theorems/graphs/build_d16D5_n33792.py`): K~3,3~ with a doubled perfect matching,
lifted by Z~22~ (66 + 66 controller vertices), fibre F~4~^4^, with edges ((a~i~, g), x) ~ ((b~j~, g + v), A~c~x + λb~c~),
λ in F~4~. It has 33,792 vertices, is 16-regular, has diameter 5, and every vertex has one spare degree when Δ = 17.

**Proposition (hubs).** Let G be bipartite with sides A, B and diameter 5. Add new vertices (hubs): a hub on side A
is joined to a set N ⊆ B, a hub on side B to a set N ⊆ A, each old vertex in at most one N. If (1) every vertex of the
hub's own side is within distance 3 of N, and (2) any two hubs on the same side have neighbours x, x′ with
d~G~(x, x′) ≤ 2, then the new graph has diameter ≤ 5.

*Proof.* Old pairs keep their distance. A hub h on side A reaches all of A within 4 by (1), and all of B within 5,
since distances between B-vertices in G are at most 4 (G is bipartite with diameter 5). Two A-hubs are within 4 by
(2). An A-hub reaches every A-vertex within 4, so it reaches every B-hub, which has a neighbour in A, within 5. ∎

The two sides are independent, so the best packings of each side combine. With |N| = 16 the maximum degree is 17.

**Hubs from fibre lines, in orbits.** A set N of 4 affine lines {(v, y + λc) : λ ∈ F~4~} in 4 controller vertices
covers a whole side within distance 3 for many choices (squad card r1/c03). Translation g ↦ g + 1 on the controller
coordinate is an automorphism of the base, so a good N gives 22 hubs at once (card r2/d06), provided its translates are
disjoint and pairwise compatible. Each orbit uses 16 of the 768 "keys" of its side, so a side holds at most 48 orbits,
and the method is capped at 33,792 + 2 · 48 · 22 = 35,904 vertices.

**Packing.** Greedy growth of orbit bases saturated at 32 orbits on side A and 37 on side B. Destroy-and-repair loops
(drop 2–5 orbits, regrow for 60 s, keep if not worse), an annealer over orbit packings, and "region" destroys (drop
every orbit meeting a random affine set of keys) brought side A to 43 orbits and side B to 45: 88 orbits, 1,936 hubs,
35,728 vertices, 25.6 % of the Moore bound. Twelve more search cards in a fifth round found no 44th or 46th orbit.
Master has the earlier 35,618 (83 orbits), checked all-pairs by the coordinator; 35,728 is checked all-pairs by the
session, by a separate plain BFS from every vertex (`bfs_all`), and by this job.

## 5.5 The other rows

- **(18,5), (19,5): doubled-matching lifts of W(q)** (`research/frontier/beyond/MDM.md` on the branches,
  `research/d10D7/DM_D5.md`). With k doubled matchings over Z~2~ × Z~2k+1~ the lift of the symplectic quadrangle W(q)
  has degree q + 1 + 2k and 4(2k + 1)(q + 1)(q² + 1) vertices, and diameter ≤ 5 as soon as one parity labelling of the
  flags splits the q + 1 geodesics of every opposite pair; the matchings can be anything. (18,5): q = 13, k = 2;
  (19,5): q = 16, k = 1 (Z~6~).
- **(20,5): route-chart lift over F~5~.** The (16,5) construction with fibre F~5~^4^ and 4 letters × 5 scalars,
  controller K~3,3~ + doubled matching lifted by Z~20~ (60 controller vertices per side).
- **D = 6.** H(q) for q = 16, 17, 19 are Moore graphs; (19,6) is Theorem D of the lab's polished notes (the hexagon H(17)
  doubled with levels and an exact whisker set), proved for odd q and checked in Lean.
- **D = 7.** 2r + 1 copies of H(q) joined by r matchings (section 4); for (17,7) the conics-2 job freed some incidences
  of the 7-copy cover of H(13) and used the freed slots for 32,356 + 30,327 hub vertices joined by a hub graph of degree
  at most 10 (SYNTHETIC.md §4.2), 5,693,959 against 5,631,276 for the plain cover. For (18,7), (19,7), (20,7) the plain
  covers are listed: the new-cells-beyond job did not establish the hub condition for q = 13 and 16 and expected
  gains of only 0.1–0.4 %, and the conics-2 hub construction was run for (17,7) only.

# 6. What failed

- **(17,5) before the hubs.** A fifth translation vector on one route-chart letter (17 = 5 + 4 + 4 + 4) cut the far
  pairs at Z~23~ from 106,000 to 47,000 but not to 0, and cannot repair a singular pattern that uses the extended letter
  once. Lifts of W(13) with 3 extra degrees (8 sheets): with a doubled and a plain matching the conditions force the
  labelling to be a coboundary, which kills the needed parity condition unless the matching is a polarity; on W(8),
  which has one, the far pairs fell from 174,000 to 2,432 but not to 0. In any cover of W(16) two copies of one
  vertex are at distance at least 6 (girth 8). Haar graphs: best 20,200 (AGL(1,101)). A projective-plane scaffold for
  the hubs left 12,182 far pairs. Hub packing itself sits on a plateau at 43 + 45 orbits.
- **Larger μ at D = 11.** (12,11) SL(2,601) × Z~7~ (μ 10.7) stopped at 2 holes after about 230 evaluations and
  SL(2,193) × Z~211~ (μ 10.3) at 2 with −I its only hole; (11,11) PSL(2,257) × Z~73~ (μ 10.1) stopped at 9, while
  SL(2,853) at the same μ solved after 892 evaluations. The later job beyond-d11b did not try to raise
  (11..14, 11) or (11,12): the gains would be 1–3 % and its machine was busy with the 30-billion-vertex checks.
- **Near misses that did not close** (1–3 uncovered elements): (6,11) SL(2,103), (7,11) SL(2,67) × Z~19~, (9,11)
  SL(2,137) × Z~31~, (6,12) PSL(2,211), (9,12) PSL(2,167) × Z~241~, (6,13) SL(2,59) × Z~103~ (the two holes are a
  transpose pair), (6,14) PSL(2,83) × Z~331~, (7,13) PSL(2,131) × Z~139~; and (9,13) SL(2,677) × Z~13~ stopped at 12.
- **Other shapes for S.** Orbits of size 2, 4, 5, 6 at D = 11; transpose-closed S; −I as a generator; orbit-closed S
  inside metacyclic groups; a meet-in-the-middle finisher. None beat the order-3 orbits (in SL/PSL) or random S (in
  metacyclic groups). Near the limit the annealer's 1- and 2-hole states are real local minima: all 105,609
  single-generator swaps of a 1-hole (4,12) state were tried and none closed it.
- **Other groups and bases.** Metacyclic groups at Δ ≥ 6 (except (6,11)); Frobenius groups at (7,11) and (8,11)
  (2 and 8 holes); non-abelian voltage groups on GP(10,3) (2 holes at 3,300 vertices); in beyond-d11b's first round
  Sz(8), F~p^3^ ⋊ C~k~, bipartite Cayley graphs of PGL(2,p), PSL(2,p^e^) with a field automorphism, AGL(1,q) products,
  and voltage lifts of PG(2,3) (19,500 at (4,11)).
- **D = 8 from hexagons.** The 2013 table's D = 8 values follow a pattern (2j + 1)(⌊(q − 1)/2⌋ + 3(j − 1))·|H(q)| whose
  construction we do not know. Card r1/c10 of new-cells-beyond found a Z~20~ lift of H(3) plus two matchings with
  diameter 8 (14,560, the pattern's value at q = 3) by annealing, but q = 4 stalled at 150 holes. Such a construction
  would give about 1.6–1.9 times the Haar values at D = 8 (for example about 2.2 · 10^8^ at (20,8) against
  1.2 · 10^8^).
- **D = 5 otherwise.** Route charts over F~3~ (6 letters) and F~2~ (9 letters) reached only 29,160 at (18,5) in
  25-minute runs. Blind annealing of voltages on W(13) stayed in the millions of uncovered pairs where the structured
  doubled-matching lift solves in seconds.
- **The machines.** Four cores and 15 GB per cloud session. A 20-billion-vertex check was killed once for memory when
  a squad card's checker and a search ran beside it; squad cards were then capped at 0.5 GB, which also capped what they
  could search at (7,14) and (8,13). Checking time grows with p as well as N (haarcheck_gen's field tables leave the L2
  cache near p ≈ 850–1,000): the 14.4-billion-vertex (14,11) check took about 4.4 CPU-hours.

# 7. Loose ends

1. The reference check (sl or psl, two halves) of (16,11) and (10,13).
2. An exact check of the three level graphs at D = 7, or the hub step of (17,7) applied to them.
3. The coordinator's own check and recording of (17,5) 35,728 and (3,11) 1,474, which are above master's values, and
   of the D = 13, 14 values that are still only on the beyond-d13 branch.
4. A literature check for all 64 cells, cubic cells first.

# 8. Files

- Table rows and PDF: `research/paper/make_beyond.py` (re-derives every vertex count and percentage; `--pdf` runs
  pandoc and tectonic). This note: `research/paper/BEYOND.md`, `BEYOND.tex`, `BEYOND.pdf`.
- Second checks of this job: `research/paper/beyond_checks/` (README there).
- Haar solution files: `research/frontier/sols/d<Δ>D<D>_*.txt` (master for D ≤ 12 except (16,11); the beyond-d13
  branch for D = 13, 14; the beyond-d11b branch for (16,11)). Rebuild and check one with
  `python3 research/frontier/build_haar2.py FILE` (small) or `cc -O3 -o sl research/frontier/haarcheck_sl.c && ./sl FILE`.
- Edge lists: `research/frontier/beyond/graphs/` (master and branches), `research/frontier/beyond13/graphs/`
  (beyond-d13), `research/squads/beyond-small/graphs/` (beyond-small); check with
  `cc -O3 -o apsp research/lifts/coordinator_check/apsp.c && ./apsp EDGES Δ D`.
- Squad logs: `research/squads/LOG.md` and `research/squads/beyond*/` on each branch.
