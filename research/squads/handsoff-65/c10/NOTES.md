# c10 notes: augmented quotient bases of the 684 Haar graph (round 2)

Idea (card c10): the 684 graph H = H(G,S), G = SmallGroup(342,12) = C6 x (C19:C3), S = {113,16,280,65,59,295}, is a regular
N-cover of its quotient by a normal N (bases from c9's normals342.txt; `quot.py`). Add j new vertex pairs to the base,
rewire 6 base edges (a new pair a (side 0), b (side 1): a takes 6-nab freed side-1 ends, b takes 6-nab freed side-0 ends,
nab parallel a-b edges), and lift by N: n = 684 + 2 j |N|. Every move stays N-equivariant.

## Files
- bases/qL.base, bases/nL.tab: quotient bases for normal subgroup line L of normals342.txt (quot.py, NORM=normals342.txt).
  L2 = C2 (342+342 base, n 688 after augmentation), L3 = C3 (228, 690), L4 = C6 (114, 696), L5 = C19 (36, 722),
  L7 = C19:C3 (12, 798), L13 = C57 (12, 798). All six quotient bases lift to the 684 graph (vl EVAL cost 0).
- augment.py IN OUT NAB SEED PAIRS M: the augmentation above (nab = parallel a-b edges; new voltages random in Z_M).
- fam.sh L NAB SEED SECS T0 T1: augment + vl SA (FIXTREE=0), appends to runs/log.tsv.
- evalb.sh SOL TAB: lift a vl solution (lift.py) and print n and far pairs (score65).
- gauge.py: abelian gauge normalisation (tree voltages to 0) for tabu (INIT=sol needs it).
- randvolt.py: random voltages on a base.

## Calibration
- Unaugmented bases: vl cost 0 for all six (the 684 graph). OK.
- Random-start SA on the 36-vertex C19 base (no augmentation): best 266 (SA 60 s, T0=3), 322 (T0=5), 530 (T0=20); tabu
  216 in 60 s. So the 684 structure is NOT found from random starts; the search must start from the quotient solution.
  Tabu (shared/tabu) is slow here: about 1.6 steps/s on 108 edges.
- Bad pairs vs vl cost: bad ~ cost * m / 2 (e.g. C19 cost 364 -> bad 3458; C6 cost 412 -> bad 1236).

## Family results (vl SA, FIXTREE=0; bad = far pairs from score65; bad ~ m*cost/2)
| family | n | augmentation (random removal, 30-200 s SA) | bad |
|---|---|---|---|
| C2 (L2) | 688 | nab=1, 240 s, random start | 502 (cost 502) |
| C2 (L2) | 688 | nab=1,3 random start, 200 s | 501 / 514 |
| C3 (L3) | 690 | nab=1, 30 s | 807 |
| C6 (L4) | 696 | nab=2, 30 s | 1236 |
| C19 (L5) | 722 | nab=1, 30 s | 3363 (cost 354-372) |
| C57 (L13) | 798 | nab=1, 20 s | cost 206 (bad ~ 5800) |
| C19:C3 (L7) | 798 | nab=2, 20 s | cost 224 (bad ~ 6400) |

## Why the equivariant route is expensive (measured)
- Deletion damage of ONE base edge of the quotient (vl cost with that edge removed, dmg.py), per family:
  C2 88-166, C3 88-166, C6 88-166, C19 94-176, C57 110-180 (vl units). In bad pairs one base edge = |N| lift edges, so
  about 44 bad pairs per deleted lift edge, the same number c7 measured for the 684 graph (44-83).
- An equivariant pair insertion (nab=0) must delete 6 base edges = 6|N| lift edges (C2: 12 lift edges, about 500 bad
  pairs). Unconstrained surgery (c7) deletes 5 lift edges for n=686, so the quotient route is dominated.
- Random removal, C2, 688: EVAL start cost 465-560 (40-150 samples); SA does not get below about 450.
- Damage-guided removal (augdg.py: 6-nab edges drawn from the K lowest-damage base edges, dmg_L2.txt), best of 300 EVAL
  samples: nab=0 401, nab=1 368, nab=2 326, nab=3 372. Low-temperature SA (T0=2, T1=0.2, 200 s) from the nab=2 start:
  324. Candidate: a688_bad324.edges (score65: n=688, bad=324, simple, bipartite).
- Random-start SA on the unaugmented C19 base does not find the 684 solution (best 266 at 60 s, T0=3), so every search
  must start from the quotient solution.

## Follow-up (18:30-18:40)
- nab=2 damage-guided start (326) + low-T vl SA 200 s: 324 -> a688_bad324.edges (scoreboard line added).
- Unconstrained 2-switch SA (c7 sa.c, copied as sa7.c) from the 324 graph: T0=1 no move below 324 (150 s, 97k evals);
  T0=6 wanders up to 385, best stays 324. Guided SA (c7 gsa.c as gsa7.c, K=100, T0=2, T1=0.3, 150 s): 324 -> 320
  (runs/gsa_688.edges). Acceptance is 4 of 280000 at T=0.3: the 688 point is a deep 2-switch local minimum.
- Sampling 3000 damage-guided nab=2 starts (samp/bestdg_L2_n2.base) is running in the background.

## Best so far (18:30-19:05)
- Damage-guided start (3000 EVAL samples, nab=2, 6-2=4 removed base edges from the 20 lowest-damage edges, C2 688):
  best start cost 318. Low-T vl SA 200 s: 314. File a688_bad314.edges (score65: n=688, bad=314, simple, bipartite).
  Scoreboard lines added for 688 bad 454, 356, 324, 314 (each a personal best in this folder).
- Guided SA (c7 gsa, 150 s) from 314: no change (278706 steps). Reheat vl SA (T0=3, 270 s): 314 again.
- Exhaustive 2-switch scan (c7 scan3, copied as scan3c; 240 s, 800930 valid switches over the first 447 of 2064 edges):
  no improving 2-switch; 38 switches with +1..+19, 1116 with +20..39. So 314 is a 2-switch local minimum (on the scanned part).
- Other families with the same method (damage-guided start, low-T SA):
  C3 (690): start 306, SA 300 -> bad 450 (a single vl cost unit = 1.5 bad pairs).
  C6 (696): start 312, SA 281 -> bad 843 (3 bad pairs per unit).
  C19 (722), C57/C19:C3 (798): not repeated with damage guidance; random-start costs were 354-372 (bad ~3300) and 200+ (bad ~6000).
- Ranking by far pairs at n > 684: C2 688: 314, C3 690: 450, C6 696: 843, C19 722: ~3300, C57/C19:C3 798: ~5000+.

## Verdict on the card
- The C19 family (722) gives far more pairs than C2 (688) because each base-edge deletion removes |N| lift edges.
- No N-equivariant augmentation reached bad 0 or below c7's 177 at 686. The best candidate is a688_bad314.edges (not a
  record). The lesson: an equivariant insertion removes 6|N| lift edges at about 44 far pairs each, while unconstrained
  surgery (c7) removes 5 lift edges for one pair at n=686.

## Next ideas (not done)
- Damage-guided removal with the non-symmetric 2-switch SA (c7-style) starting from the 688 symmetric solutions.
- Larger samples (10^4) of damage-guided removal with nab=2 for C2; probably gains of 5-10 pairs only.

## Final checks (19:00-19:20)
- Low-damage pool of 10 (K=10 lowest damage): start 324, SA 320 (runs/L2_k10.sol).
- Base 2-switch moves (SWAP=0.05) from the 314 graph: still 314.
- Cooler SA (T0=1.5) from the 3000-sample start: 314 again (same local minimum).
- Exhaustive over the 2^10 voltage patterns of the 10 new edges (enumv.py) for the 318 removal set: best 314, so the SA
  had already reached the best voltages for that removal set.
- Exhaustive 2-switch scan (scan3c, 240 s, first 447 of 2064 edges): no improving switch.
- Final candidate: research/squads/handsoff-65/c10/a688_bad314.edges (n=688, bad=314). Not a record.
- 19:24: 1200 more damage-guided samples (seed 7000, KT=15): start 314; SA 170 s -> 312 (a688_bad312.edges, scoreboard line added).

## Final state (19:31)
- Best: a688_bad312.edges (n=688, bad=312, simple, bipartite, maxdeg 6), from the C2 family (Z2-lift of the 684 graph, one
  base pair, 4 base edges removed from the 15-20 lowest-damage edges, 2 parallel a-b edges). Not a record.
- Other seeds of the same method: 314, 320, 324, 326. A second SA from 312 (new seed): 312.
- Families at n > 684 by far pairs: C2 688: 312; C3 690: 450; C6 696: 843; C19 722: about 3300; C57 and C19:C3 798: over 5000.
- No N-equivariant route reached bad 0. Equivariant insertion costs about 44 far pairs per deleted lift edge and removes
  6|N| lift edges, so these families are dominated by unconstrained surgery (c7: 5 lift edges, 178 at 686).
- Scoreboard: c10 lines for 688 with bad 454, 356, 324, 314 and 312 (added in this order).
- No background processes of mine remain (the tabu processes in the list belong to another worker).
- 19:37: three more anneals from the 312 graph (SWAP=0.1 T0=3; T0=1 cool; 170 s each): 312. Stopped; no processes of mine remain.
