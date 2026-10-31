# six-five-384: Haar graphs of degree 6 and diameter 5 on 768 vertices (Oct 31, 2026)

Goal: a bipartite graph of maximum degree 6 and diameter 5 on more than 684 vertices (table value 684, a Haar graph
of C6 x (C19:C3) = SmallGroup(342,12)). Earlier jobs (branch claude/squad-6-5-rounds-ts5nxk, research/s65/README.md)
closed every degree-6 Haar graph on 686-800 vertices except those of order 384 (20,169 groups, 768 vertices). This job
closes order 384. Squad rounds: research/squads/s384r1, s384r2 (log in research/squads/LOG.md).

**Result: no Haar graph of degree 6 and diameter 5 on 768 vertices** (all 20,169 groups of order 384 closed: 2,765 by
exact filters, 17,404 by exhaustive search), **and none on 802-900 vertices** (all 2,742 groups of order 401-450 closed,
an extension beyond the brief). With research/s65 this closes every Haar graph of degree 6 and diameter 5 on 686-900
vertices: the 684 record is the largest such Haar graph up to 900 vertices. `python3 src/coverage.py` and
`python3 src/coverage_gen.py` regenerate the coverage tables from the logs.

## What is searched

H(G,S) for |G| = 384, S a 6-subset of G: vertices G x {A, B}, (g, A) ~ (s g, B). H(G,S) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G (right multiplication is transitive on each side; odd distances follow). Every
graph with a group of automorphisms acting regularly on both colour classes is such a Haar graph, so this also covers
the bipartite Cayley graphs on 768 vertices (a bipartite Cayley graph of a group of order 768 is a Haar graph of its
index-2 subgroup) and all vertex-transitive graphs on 768 vertices with such a subgroup.

## Setup

- GAP 4 from pip (`pip install passagemath-gap`, which bundles the SmallGroups data); run as
  `site-packages/gap/gap -l site-packages/gap -A` (`-A`: the bundled ctbllib has no data and breaks autoloading).
- `src/inv384.g`: invariants of all 20,169 groups (`data/inv384.txt`: abelian invariants, r2 = rank of G/G'G^2,
  number of involutions, |Z|, normal Sylow 3, IdGroup of G/O_3(G), derived length).
- Exports (multiplication table with identity = 0, then Aut(G) generators as permutations): `src/hx_export_batch.g`
  (full table), `src/hx_export_pc.g` + `src/hxexpand.c` (compact: right multiplication by the pc generators and the
  exponent vectors; hxexpand builds the full table and checks identity, Latin square and that every automorphism
  preserves the table; byte-identical to the full export on 6 groups), `src/hx_export_any.g` (other orders).
- Pipeline: `src/pipe_export.sh` (GAP exporter, queue) and `src/pipe_worker.sh` (3 workers: hxexpand, haarex, log).
  Logs: `logs/h384_<id>.log` (haarex output without the PAIR lines, plus run time).

## Exhaustive search programs

All three run the same orderly enumeration as research/s65/tools/haarex3.c (job squad-6-5), which itself is haarex2
(job fresh-6-5) with the last element solved: S = {e, r, r2, a, b, c}, (r, r2) over class minima of ordered pairs under
Aut(G), prefixes pruned when a transform (P t^-1, t^-1 P, P^-1 t, t P^-1) has a smaller pair class, the last element
c solved exactly from the targets missed by the 5-prefix, side B checked for every side-A cover. Output lines: VALID
(both sides covered), ASIDE (side A covered, side B fewer than 4 short), DONE (pairs, prefixes, Acovered, valid).

- `src/haarex4.c`: x-independent products precomputed per prefix, transposed table, targets in move-to-front order,
  per-candidate tests when at most 6 candidates are left, lazy Q5 Q5 membership test. About 2x haarex3.
- `src/haarex5.c` (squad card s384r1-c1): per 4-prefix {e, r, r2, a}, the b-free part A4(x) of each target's solution
  set is cached; per b only the words containing b are added; bad(S,5) checks only the terms with b. About 1.5x.
- `src/haarex6.c` (squad card s384r2-c1): haarex5 with byte arrays instead of bitsets (store-only marks; squad card
  s384r1-c2's low-level changes). About 1.2x. The order-384 sweep ran haarex4 on 320 groups, haarex5 on 1,438 and haarex6
  on 15,646 (the program is named in the first line of each log); orders 401-450 ran haarex6.

Calibration (identical VALID/ASIDE/PAIR/DONE output, and identical prefix counts, for haarex3, 4, 5, 6):
SmallGroup(342,12) (the 684 record: 10 VALID sets), 360_53 (41 side-A covers, 12 ASIDE lines), the other groups with
side-A covers found by squad-6-5 (360_55, 360_56, 360_125, 360_126, 360_136, 360_138, 372_1), and order-384 groups
(11094, 10494, 10694, 10894, 11818, 12518 for haarex3/4; 10494, 12518, 10694, 11094 for 5/6). Benchmark script used
by the squad: /tmp/claude-0/bench/bench.sh (copied to `src/bench.sh`).

## Filters (exact)

Every element of G is the value of one of the 781 non-backtracking words of length 0, 2, 4 on each side (e,
s_b^-1 s_a, s_a^-1 s_b s_c^-1 s_d with a != b, b != c, c != d; side B: e, s_a s_b^-1, s_a s_b^-1 s_c s_d^-1).

1. **Rank.** If G/G'G^2 = C2^r with r >= 5: the image of (S^-1 S)^2 in C2^r consists of sums of even subsets of size
   <= 4 of the 6 images, at most 1 + 15 + 15 = 31 < 32 elements. Excludes 1,842 groups (r2 = 5: 1,806; 6: 34; 7: 2).
2. **Quotient counting** (`src/qfeas.c`). For N normal, Q = G/N, every coset needs >= |N| of the 781 words, on both
   sides, for some image 6-tuple (q_1 = e by left translation, q_2 up to Aut(Q), q_3..q_6 a multiset). Results
   (`data/qfeas/`): order 32 (T = 12): only C2^5 fails; order 48 (T = 8): none fails; order 64 (T = 6): 64_193,
   64_194, 64_202 fail (best minimum 5) besides the rank-5/6 groups 64_260-267; order 96 (T = 4): D96 = 96_6 and
   C2 x D48 = 96_110 fail (best minimum 2) besides 96_207, 96_230, 96_231. Cross-check: 64_193 with the automorphism
   reduction switched off gives the same verdict and the same best minimum.
   Use: a quotient of order 64 of a group of order 384 has a kernel of order 6, which contains the normal C3, so it
   is a quotient of P = G/O_3(G) by a central C2 (`src/q64filter.g`, `data/q64of128.txt`). 135 of the order-128
   groups P have 64_193, 64_194 or 64_202 as such a quotient; this excludes 923 order-384 groups with r2 <= 4.
   (The order-96 failures were not applied: the dihedral quotients need exponent divisible by 24 and the few groups
   with them are in the exhaustive sweep anyway.)
   Squad card s384r1-c6 wrote an exact test for |Q| = 128, T = 3 (research/squads/s384r1/c6/qf128.c): 138 of the 150
   most frequent order-128 quotients pass, 128_2046 fails (16 groups); not used here (those groups are in the sweep).
3. Abelian quotients do not help much: in C2^4 (T = 24) 89% of the image 6-tuples with distinct images pass.

`data/excluded.txt` lists the 2,765 excluded ids with the reason.

## Coverage (order 384)

`data/coverage384.txt`: one line per id (method, and for exhaustive runs the number of pair classes, prefixes,
side-A covers and VALID sets).

| method | groups |
|---|---:|
| rank filter (r2 = 5, 6, 7) | 1,842 |
| quotient filter (64_193, 64_194, 64_202) | 923 |
| exhaustive (haarex4/5/6) | 17,404 |
| open | 0 |
| total | 20,169 |

No VALID set and no ASIDE line (side A covered with side B fewer than 4 short) in any log. 45.3 billion 5-prefixes,
17.2 CPU-hours of search (plus GAP exports). Side A, (S^-1 S)^2 = G, is covered in only 7 groups (side B then at least
4 elements short), all with 3-15 involutions:

| id | side-A covers | involutions | G/G' | structure (GAP) |
|---:|---:|---:|---|---|
| 1098 | 17 | 3 | C2 x C2 x C4 | C3 : ((C4 x C2) . (C2 x D8)) |
| 2677 | 57 | 7 | C2 x C2 x C4 | C3 : (C2 . ((C4 x C2 x C2) : C4)) |
| 2705 | 78 | 7 | C2 x C2 x C4 | C2 x (C3 : (C2 . ((C2 x C2 x C2) : C4))) |
| 5556 | 9 | 7 | C2 x C2 | (C4 x C4) : (C3 : Q8) |
| 5669 | 8 | 3 | C2 x C2 | (C2 x C2) . ((C2 x C2) : S4) |
| 5798 | 32 | 7 | C2 x C2 x C3 | (C4 : (C4 : Q8)) : C3 |
| 18177 | 99 | 15 | C2 x C2 x C2 x C3 | Q8 x (((C4 x C2) : C2) : C3) |

## Orders 401-450 (802-900 vertices)

The brief noted that orders 401-450 were covered only by the self-dual sweep of research/selfdual-d5. Since the
pipeline had spare capacity, all of them were closed with haarex6 (`src/pipe_export_gen.sh`, `src/pipe_worker_gen.sh`,
`src/hx_export_gen.g`; full-table export for the non-solvable groups, e.g. 420_13; logs in `o401_450/logs/`, coverage
in `o401_450/coverage.txt` and `o401_450/coverage_table.md`): 2,742 groups, 105 abelian (at most 542 vertices, job
fresh-6-5's counting bound), 28 excluded by the rank filter (27 of order 448, 1 of order 416), 2,609 exhaustive.
No VALID set, and no side-A cover at all.

## Record-check pipeline (ready, not needed)

`src/haar_record.sh ORD ID EXPORT OUTDIR s1..s6` builds the edge list from the export table (`src/haar_table_edges.py`)
and independently from GAP's group arithmetic (`src/haar_gap_edges.g`), compares the sorted edge sets (sha256) and runs
research/lifts/coordinator_check/apsp.c at d = 6, D = 5 and D = 4. Calibration on a VALID set of SmallGroup(342,12):
builders agree, VALID at D = 5, INVALID at D = 4 (`data/record_pipeline_calibration_342_12.txt`). No record was found,
so `records/` is empty.

## Other results of this job

- Tabu local search (squad card s384r1-c8) on 60 order-384 groups: best |G \ (S^-1S)^2| + |G \ (SS^-1)^2| = 8
  (384_18), median 23; on the 684 record group it reaches 0 in about 3 s. The closest groups were closed by the
  exhaustive search.
- The 704-vertex 2+2 lift by C11:Q16 (lift cost 4, the closest graph above 684 from squad-6-5) is an isolated local
  minimum: every 1-change costs >= 10, exact search over all pairs of voltage changes and over all values of four
  voltage triples finds nothing below 5 (squad card s384r2-c4).
- Lifts of the GQ(5,5) incidence graph (312 vertices) by a group of order 3 cannot have diameter 5: two collinear
  points are joined by a single walk of length <= 4 up to backtracking (no triangles), so a point reaches only one of
  the three lifts of a collinear point within distance 4.
- Counting bound for orbit structures (squad card s384r2-c8, checked by hand for 1+2): a graph of maximum degree 6 and
  diameter 5 with a group acting semiregularly with k_A orbits on one colour class and k_B on the other has at most 249
  vertices for 1+2 orbits, 650 for 2+3 and 108 for 1+3; above 684 only 2+2, 3+3 and 3+4 remain, and 3+4 would need
  about 75% of the Moore-type count of a B-vertex (the 684 record uses 44%).

## Notes for the next job

- Haar graphs: closed up to 900 vertices. haarex6 handles N <= 512 (W = 8 words); orders 451-512 (902-1,024 vertices)
  would take a few hours with the same pipeline (order 480 has 1,213 groups, 500 has 56; 512 has 10,494,213 groups and
  would need the rank filter plus much more).
- Machine: the cloud kernel uses autogroup scheduling, so `nice` inside one session does not lower its priority against
  another session's processes; use `echo N > /proc/<pid>/autogroup` (done here for the squad cards and the pipeline).
