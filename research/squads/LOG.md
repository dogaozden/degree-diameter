# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-28, job thm-polygon-levels (Opus director, branch claude/haiku-squads-diameter-7-hr64vz), round polylev r1

Goal: colourings for the D = 9 ball lift of H(q) (k balanced dominating classes of points and lines; records need
k/(q^2+q+1) between 49% and 97%) and the D = 11 lift (K disjoint lines + K non-collinear points); small-q theorem tests.
16 Haiku cards (model haiku), header research/squads/polylev/r1/HEADER.md, scoreboard r1/scoreboard.jsonl.
Machine: 4 cores, load 11-16 during the round (too many heavy cards for the cores; the q = 13/16 cards also lost
their time box waiting for group data that the director's Python generator produced too slowly, and for q = 13/16 it
first had a bug: the Singer search never ended when q = 1 mod 3).

| card | idea | best | verdict |
|---|---|---|---|
| c01 | clause-weighting local search | q=3 lines k=11: cost 9 (plain 16); no new k | helps a little, no solution |
| c02 | packings of Hermitian spreads at q=9 | 1 (no two disjoint; overlaps 1 or 10) | rules out ovoid/spread packings at q=9 |
| c03 | S7-block colourings q=9, k=63/70; SA variant | cost 79,371 (k=63) | far from 0 |
| c04 | S7-orbit-invariant q=9, k=63 | cost 140,829 initial, no solution | far |
| c05/c06 | q=11 S7 blocks k=84 points/lines | cost about 287,000 each | far |
| c07/c08/c09 | q=13 / q=16 | not run (input not ready in time) | - |
| c10 | q=16 lines S91 k=182 | cost 386,919 at 87 s | far |
| c11 | D=11 q=7 max disjoint lines / non-collinear points | 1,619 / 1,618 (66%; 76% needed) | short |
| c12 | D=11 q=8, Singer-73 orbit quotient + ILS | 2,701 both (65%; 71.5% needed) | short; best idea of the round |
| c13 | theorem tests: D=9 at q=4 (k=13, r=1,2) | 73,710 and 144,690 vertices, diameter 9, D=8 fails | confirms Cor. 3.1 |
| c14 | theorem test: D=10 spread stars q=2,3 | 4/4 graphs, diameter 8 and 9 (<= 10) | confirms Cor. 4.4 |
| c15 | wildcard (algebraic colourings, projection codes) | see r1/c15 | no k beyond local search |
| c16 | prior art | Delorme 1985 EJC §4(c) G*C35: D=9, degree q+3, 70N; nothing on partitions of H(q) | credited in the note |

Kept: c12's orbit-quotient method (for D = 11), c13/c14 as theorem checks, c02 and c16 for the note. Next: the director
measured how k scales with q at fixed ratio (q^2+q+1)/k before deciding on a production run at q = 16.

## 2026-10-28, job thm-polygon-levels (Opus director, branch claude/haiku-squads-diameter-7-hr64vz), round polylev r2

Goal: D = 11 first values at (Delta, 11), Delta = 11..20 (no lab values there), the cells (9,11) and (10,11), and small
D = 9 measurements. 16 Haiku cards (model haiku), header research/squads/polylev/r2/HEADER.md, scoreboard
r2/scoreboard.jsonl. Machine: 4 cores; load reached 28 when all cards ran heavy C jobs at once, which starved the
director's own runs and made several cards lose wall-clock time (lesson: at most 4-6 heavy cards per round on this
machine, or give each card a CPU budget instead of a wall budget).

| card | idea | best (certified) | verdict |
|---|---|---|---|
| e01 | greedy + 1-2 swap ILS, all t.s. lines, q=11 | 8,257 lines | superseded by e15 |
| e02 | q=11 points, orbit quotient of a group of order 399 (Singer 133 + normaliser) | 8,379 points | used (q=11 K) |
| e03 | q=13 greedy disjoint t.s. lines via 4-walks | 15,536 lines | used |
| e04 | q=13 points, Singer-61 quotient + ILS | 14,335 points | used (q=13 K) |
| e05 | q=16 greedy rounds of t.s. lines | 32,391 lines | used |
| e06 | q=16 points, S91 quotient + ILS | 28,483 points | used (q=16 K) |
| e07 | q=7 points, quotients of orders 43 and 19 | 1,720 | short of 1,852 |
| e08 | q=8 points, quotients (S73, T57, T19) + full ILS | 2,907 | short of 2,975 (closed later by the director, below) |
| e09 | ILS on all t.s. lines (ils_lines.c), q=7, 8 | 1,978 (q=7), 3,255 (q=8) | used at q=7; tool reused at q=9 |
| e10 | D=11 theorem test q=3, r=1,2, own builder | 114,296 and 227,864 vertices, diameter 11 | confirms Cor. 5.5 |
| e11 | D=9 points q=5 | k=15 (16 fails, 2 seeds) | measurement |
| e12 | D=9 points q=7 | k=20 (24 unresolved) | measurement |
| e13 | q=4 non-collinear points | 273 = distance-2 ovoid (known to exist) | rediscovery, credited |
| e14 | D=9 from 5-space sections + repair | k=13 at q=4 | no gain over translocal |
| e15 | q=11 / q=7 t.s. lines, orbit packing (T133, T43) | 9,975 (q=11), 1,935 (q=7) | used at q=11 |
| e16 | domatic local search on lines (non-pencil classes), q=7 | 1,385 classes | worse than pencils |

Kept: the orbit-quotient method (e02, e04, e06, e07, e08). Director follow-up after the round: quotients by the
cyclic group of order q^2-1 of G_2(q). At q=8 its point quotient (572 admissible orbits) gave 4,041 non-collinear
points (97% of 4,161) and its quotient of all t.s. lines (tsorbq.c, 36,463 orbits) 3,285 disjoint lines, so K = 3,285
and (10,11) = 492,154,758 > 445,709,568 (note §5, Computer-checked 5.8); a warm-started ILS on all t.s. lines then
added 7 lines: K = 3,292, (10,11) = 493,203,330. The same group at q=7 (order 48), q=9 (order 80) and q=16 (order 255)
gave 71%, 62% and 44% (q=16 still improved K from 28,483 to 29,087); (9,11) stays open at K = 1,743. SAT on the
quotients (CaDiCaL via pysat): no invariant point set with 66 full orbits of order 63 at q=8 (UNSAT), one with 65
(4,095 points); the line versions (invariant near-spread, Singer-73-invariant spread, packing >= 58 orbits) and the
q=7 packings needed for (9,11) were undecided within 10-100 minutes each.
