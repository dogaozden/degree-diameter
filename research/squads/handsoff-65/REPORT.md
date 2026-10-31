# handsoff-65: a hands-off Haiku squad on the (6,5) cell (Oct 31, 2026, 15:38-21:10 UTC)

Target: a bipartite graph with maximum degree 6 and diameter 5 on more than 684 vertices (table value 684, a Haar graph
of C6 x (C19:C3) = SmallGroup(342,12)). Format of the experiment: Opus 5.5 only planned, checked in, verified and
redirected; 28 Haiku runs did the searching. Files: `cards.md` (all 28 cards), `scoreboard.tsv`, `checkins.md`, one
folder per worker (code + NOTES.md), `shared/` (tools copied from claude/squad-6-5-rounds-ts5nxk, plus check.sh).

## Result

**No record.** No graph above 684 with diameter 5 was found, so `records/` was not created. The closest graphs above 684
(I re-scored every file in this table myself with `shared/score65`; "bad" = unordered vertex pairs at distance > 5):

| n | bad | what | file |
|---|---|---|---|
| 686 | 144 | 684 graph + one vertex pair (5 edges moved), guided 2-switch SA with restarts (c7 -> c24) | c24/b686_144.edges |
| 685 | 165 | 684 graph + one A-vertex (sides 343 + 342), from c7's 686 graph minus its new B-vertex (c20) | c20/del685_0_sa.edges |
| 686 | 294 | coset graph type "1,6\|1,6" on SmallGroup(294,11): degree-5 Haar part + C6 hub orbits, mcos cost 2 (c18) | c18/cost2_294_11.edges |
| 688 | 516 | type "1,3\|1,3" on SmallGroup(258,2) = C2 x (C43:C3), cost 4 (c22) | c22/deep/t258_2_s91.edges |
| 704 | 352 | 2+2 lift by C11:Q16, lift cost 4 (c1; the same as the previous best) | c1/best704.edges |
| 728 | 546 | type "3,3\|3,3" on SmallGroup(546,15), cost 6 (c17) | c17/t728_546_15.edges |
| 732 | 915 | type "1\|3,3,3" on SmallGroup(366,2), cost 7 (c5, c12) | c5/deep/1_3-3-3.sg_366_2.best.edges |

Every one of these is a local minimum for the search that made it (exact 2-change scans in c7, c14, c24, c28).

Negative results worth keeping (worker claims with logs; I did not rerun them):
- **Haar graphs on 802-840 vertices are closed** (c19, c27): haarex3 on every non-abelian group of orders 402-420
  (353 groups: 83 in c19/STATUS.md, 270 in c27/STATUS.md; the odd orders 401-419 not listed have only abelian groups,
  which the counting bound of 542 vertices excludes), no VALID set and no side-A cover. With the
  earlier closures this makes every degree-6 Haar graph on 686-840 vertices closed except 768 (the other job's).
  Calibration: haarex3 re-finds VALID sets on SmallGroup(342,12) (apsp_ref VALID) and none on A6.
- Bi-coset |H| = |K| = 2 on all groups of order 722-766 (diagonal pairs; c4 + c15): floor cost 12 (750_6, 756_74).
- "1|3,3,3" on all tabled groups of order 345-399 with elements of order 3 (c12): floor cost 7.
- "3,3|3,3" on SmallGroup(546,15): exhaustive over one class combination (1.3e7 graphs), minimum cost 6 (c17).
- Every edge of the 684 graph is critical (deleting one costs 44-83 far pairs), so surgery that adds vertex pairs to it
  floors near 140-180 at 686 and gets worse with symmetric insertions (688: 312-320, 690: 417) (c7, c10, c13).
- Near misses (704 lift, 720 Haar of SmallGroup(360,53), 732) stay strict local minima when rewritten as lifts of
  bigger bases by subgroups (c14), and deleting vertex pairs from them gives 680-1300 (c20).
- GH(5,5) quotients (c8: built the generalized hexagon from G2(5)) and GQ(5,5) covers are far (9,520 at 686).

## Spend (tools/session_usage.py, price-weighted units, 15:38:45 to 21:06:45 UTC)

| model | messages | output tokens | cache read | units | share |
|---|---|---|---|---|---|
| Opus (coordinator) | 89 | 109,606 | 15.2M | 0.461 | 63% |
| Haiku (28 runs) | 2,281 | 2,436,065 | 322.6M | 0.275 | 37% |

So the target of about 50/50 was **not** reached: 37% Haiku. Check-in values: 35% (16:15), 44% (16:46), 43% (17:15),
40% (17:48), 41% (18:16, 18:47), 39% (19:47), 37% (21:06). The Haikus produced 22x my output tokens and 21x my cache
reads, but Opus costs much more per token, and each of my turns re-reads the whole coordinator context (about 170k
tokens on average). Most of my spend was waiting: a cloud session must not end its turn while workers run, and a Bash
call can block for at most 10 minutes, so each hour cost about 6-8 polling turns plus the turns that read the 28 final
reports and launched replacements. What I did about it: 10 workers instead of 8 from 18:20, 5-minute runs (more Haiku
turns), fewer check-ins. It was not enough. Ways to get to 50/50: a coordinator that starts a fresh short context per
check-in (scheduled wake-ups instead of a polling loop), 12-16 Haikus with lighter compute each, or Haiku cards that are
more about writing code than about waiting for runs.

## Haiku runs: 28

Round 1 (15:45-17:45): c1-c8, c9 replaced c8 at 16:25. Round 2 (17:45-19:45): c10-c16, plus c17-c19 (18:20) and c20
(19:08, replaced c16). Round 3 (19:30-21:05): c21-c28. Three runs ended in a "waiting on its own background work" state
and never sent a final report (c3, c6 in round 1 with useful notes; c21 with only a first screen). Two wildcard runs
stopped early by choice (c8 at 16:18, c16 at 18:57) despite the instruction not to.

| card | size | best (n, bad) | what it found |
|---|---|---|---|
| c1 2+2 lifts, orders 172-180 | small | 704, 352 | only order 176 is good; cost 4 always misses the same 2 fibres; = prior best |
| c2 bigger-base lifts | small | 696, 812 | doubled-K33 3+3 base by C29:C4, cost 14 (= prior); bigger bases worse |
| c3 almost simple bi-coset | large | 720, 4320 | PGL(2,13), PGammaL(2,8), A6 x C4: all far |
| c4 \|H\|=2,3 bi-coset 722-766 | large | 756, 2268 | cost 12; 3\|3 poor (182 at 722) |
| c5 multi-orbit mcos | large | 732, 915 | 1\|3,3,3 on C2 x (C61:C3), cost 7; 1\|2,2 cost 17 |
| c6 Haar + twisted matching | small | 720, 360 | no automorphism twist beats the Haar floor |
| c7 surgery on the 684 graph | small | 686, 177 | best far-pair count of round 1; strict 2-opt minimum |
| c8 wildcard: polygons | large | 686, 9520 | built GH(5,5) from G2(5); quotients far; GQ covers ruled out |
| c9 re-lift quotient bases | small | 704, 1056 | quotient bases lifted by other groups: cost 8 at best |
| c10 equivariant surgery | small | 688, 312 | C2-equivariant augmented base; dominated by critical edges |
| c11 swap-symmetric 2+2 lifts | small | 704, 2112 | symmetry hurts on non-abelian groups (cost 24) |
| c12 mixed mcos types | large | 762, 889 | wrote mtabu.c; 1\|3,3,3 floor 7 over orders 345-399 |
| c13 surgery continued | small | 688, 320 | Z2/Z3-symmetric insertion; 686 stays at 177 |
| c14 near misses as bigger-base lifts | small | 704, 352 | all near misses are strict local minima |
| c15 \|H\|=2 bi-coset, rest of 722-766 | large | 750, 2250 | 468 groups swept; floor cost 12 |
| c16 wildcard | large | 686, 1568 | Z49 lifts, stabiliser 3/4/6 bi-coset, D(3,7): all far |
| c17 tabu for coset graphs | large | 728, 546 | 3,3\|3,3 cost 6, exhaustive in one combo |
| c18 Haar + hub orbits (1,k\|1,k) | large | 686, 294 | **new family**, cost 2 on SmallGroup(294,11); wrote t18 tabu |
| c19 Haar 802-840 | large | - | orders 402-415, 417 closed |
| c20 surgery downward | small | 685, 165 | deleting from near misses fails; 685 via c7's graph |
| c21 1,6\|1,6 on 300-312 | large | - | first screen only, then stalled (no report) |
| c22 hub type k=3 | large | 688, 516 | 1,3\|1,3 on 258_2, cost 4 |
| c23 hub type k=2 | large | 720, 1080 | 1,2\|1,2 cost 15; 1,2,2\|1,2,2 cost 40 |
| c24 free local search from best | small | 686, 144 | best far-pair count of the job; acceptance rate is the bottleneck |
| c25 1,6\|1,6 on 318-342 | large | 756, 2106 | cost 18 on 324_53; the family fades with size |
| c26 non-cyclic hub stabilisers | large | 686, 1029 | S3 hubs on (C7 x C7):S3, cost 7; weaker than C6 hubs |
| c27 Haar 416-420 | large | - | orders 416, 418, 420 closed |
| c28 exact 1,6\|1,6 on 294_11/12 | large | 686, 294 | global search ~1e12 evaluations, out of reach; cost-2 states are exact 2-change minima |

## Honest view

**Did the hands-off structure do better or worse than an Opus-led squad?** On the record, the same: none, as in the
Opus-led jobs before it (fresh-6-5, squad-6-5). On breadth it did better: 28 runs covered about 20 distinct families in
5.5 hours, wrote real tools that are now in the repo (a GH(5,5) model from G2(5), two tabu searches for coset graphs
that beat mcos's annealer, an exact 2-change checker, symmetric surgery), and closed the Haar graphs on 802-840 vertices
cleanly with calibration. On depth it did worse. The Haikus followed cards literally and well, calibrated, and reported
honestly (corrections, non-monotone costs, failed calibrations were all flagged), but they rarely changed the idea when
a family stalled: they swept parameters, re-ran seeds, and declared a floor. The one genuinely new family of the day
(Haar + hub orbits, 1,6|1,6, which went from nothing to cost 2 at 686 in one run) came from a card I wrote after reading
the boards, and every lead then stopped at a local minimum that nobody had the idea to get around. An Opus-led squad
would have spent more on fewer families but would have pushed the two leads (surgery at 686 and the hub family) with
more structural thinking, e.g. choosing the inserted vertices' neighbourhoods by design, or reasoning about which hub
double cosets can cover the two missing classes. I think that is where a record would come from, if one exists. I did
not run an Opus-led squad on this goal in parallel, so this comparison is my judgment, not a measurement.

The structure also cost more Opus than planned (63%): the coordinator's waiting is expensive when every poll re-reads a
long context. Hands-off coordination would be cheaper with scheduled wake-ups and a short context per check-in.

**Small versus large structure cards.** The Haikus did better on the large-structure cards: sweeps over well-defined
families with an existing tool and a clear stopping rule (Haar closure 802-840, |H|=2 bi-coset floors, the mcos type
screens, the hub family) gave durable, checkable results, and the best structured near miss (cost 2) came from one.
The small-structure cards (surgery, local search, small-base lifts) gave the lowest far-pair counts (144 at 686) but
asked for invention, new moves and insight about why a minimum is a minimum, and there the Haikus plateaued within the
first hour and mostly reported "strict local minimum" without a way past it.
