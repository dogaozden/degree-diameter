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
