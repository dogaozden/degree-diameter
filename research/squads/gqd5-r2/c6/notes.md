# c6 (squad gqd5-r2): third-level routing at q = 7, no hubs

Instance: G = gqlib.Q4(7) (400 points, 400 lines), 7 levels, all type H, rotational tournament j -> j+1, j+2, j+3 (mod 7),
so every transition is non-friendly (H -> H). Degree 11, n = 5600. Freed set R (size s) on ONE arc (0,1) (or on 2 / 4 disjoint
arcs, same s on each). Freed = the matching edges (a, M(a)) for a in R are deleted; no hub vertices. The other 20 matchings
(and the freed arcs' matchings, with R fixed) are random bijections, then annealed. Validity = apsp checker:
`./apsp EDGES 11 5` gives RESULT VALID d=11 D=5 n=5600 (checked for every reported graph).

## Scoreboard (valid = apsp-verified)

| freed arcs | s per arc | result | file |
|---|---|---|---|
| 1 | 4 | VALID | b1_s4.edges (790 steps) |
| 1 | 8 | VALID | b1_s8.edges (2067 steps) |
| 1 | 12 | VALID | b1_s12.edges (3053 steps) |
| 1 | 14 | VALID (apsp run) | b1_s14.edges (3995 steps) |
| 1 | 16 | VALID | best.edges = b1_s16_long.edges (5481 steps, seed 1) |
| 1 | 24 | not reached: best 64 bad after 9000 steps | state_b1_s24.pkl |
| 2 (arcs (0,1),(2,3)) | 4 | VALID | b2_a2_s4.edges (1522 steps) |
| 2 (arcs (0,1),(2,3)) | 8 | VALID | b2_a2_s8.edges (4388 steps) |
| 4 (arcs (0,1),(2,3),(4,5),(6,0)) | 4 | VALID | b4_a4_s4_long.edges (3942 steps) |
| 4 | 8 | not reached: best 49 after 9000 steps | state_b4_a4_s8.pkl |

Score (one arc): s = 16. Two arcs: s = 8 each (16 freed in total). Four arcs: s = 4 each (16 freed in total), s = 8 not reached.
Also a 1-arc s=16 run with 4000 steps only reached best 61 (log_b1_s16.txt), so the step budget matters a lot.

## Bad pairs before annealing (unordered pairs at distance > 5; 3 random draws each; baseline_out.txt)

"whole" = whole graph, random other matchings (no annealing). "two-level" = only levels 0 and 1 with the arc (0,1) matching
(minus R), i.e. the two-level test with no help from other levels.

| config | whole (mean of 3) | two-level (arc (0,1)) |
|---|---|---|
| 1 arc, s=16 | 860 (884, 836, 860) | 3959 |
| 1 arc, s=32 | 1832 | 8427 |
| 1 arc, s=64 | 4039 | 18646 |
| 2 arcs, s=16 each | 1742 | 3959 (arc (0,1) only) |
| 4 arcs, s=16 each | 3480 | 3959 (arc (0,1) only) |

The other levels cut the bad pairs by a factor of about 4.6 (s=16), as with q=5 (c19). Without deletions the random graph has
0 bad pairs. Every bad pair found, before and after annealing, has an endpoint that is an endpoint of a deleted edge (a point of R
or a line of M(R)): checked on the baseline (whole = endpoint-involved for all 15 draws) and on the final states of s=16, s=8 and
two-arc s=4 (0 of 61, 0, 0 pairs outside). So the director's restriction to pairs (deleted-edge endpoint, vertex of the other
level) holds in these experiments. Note: a first local tally that suggested line-line bad pairs outside it was my indexing bug.

## Move set and annealing (sa7.py)

- Objective: exact number of unordered bad pairs in the WHOLE graph (bit-parallel all-pairs BFS, bad7.c, about 15 ms).
  The restricted (endpoint-only) count was not used, since it is only a heuristic (though it held empirically here).
- 'rand': swap the images of two random points in one random matching (about 40 ms/step, almost all moves are neutral).
- 'targ' (used for all reported results): pick a random bad pair (x, v); pick a, b with a + b <= L-1, where L = 4 if x, v have the
  same type (parity) and L = 5 otherwise; pick p in ball_a(x) (a point) and q in ball_b(v) (a line) with level(q) - level(p) in
  {1,2,3} mod 7; set M_t(p) = q by swapping with the preimage of q (t = arc level(p) -> level(q)). The new edge closes a
  path of length a+1+b <= L. SA with T0 = 1.0 linearly cooled to 0.02, 1500 to 9000 steps.
- Bug found during the work: the first version used a + b = 4 for every pair. For same-type pairs (all bad pairs here are PP or
  LL) this yields no valid candidate, so the 'targ' runs were just random swaps (s=4 stalled at 172 bad pairs). Fixed version
  (the one in sa7.py) takes s=4 to 0 in 790 steps. The table uses only the fixed version (logs b1_*, b2_*, b4_*).

## Files (all in research/squads/gqd5-r2/c6/)

- common7.py (q=7 level graph, bad-pair counting), bad7.c / bad7.so (all-pairs bit-parallel counter), sa7.py (annealing;
  usage: `python3 sa7.py targ <arcs 1|2|4> <s> <steps> <seed> <T0> <tag>`), baseline7.py (baseline counts), chain.sh (batch).
- best.edges: copy of b1_s16_long.edges (one arc, s = 16, n = 5600, apsp VALID d=11 D=5).
- state_*.pkl: M, R, best for each run. log_*.txt: annealing traces.
- Killed/buggy runs: log_a1_s16.txt (random-swap 'mix' run, stopped at it ~2700, best 492), log_a1_s4.txt (killed, see Bugs above).

## Reproduce the score

    cd research/squads/gqd5-r2/c6 && python3 sa7.py targ 1 16 9000 1 1.0 b1_s16_long   # ~4 min, one core
    ../../../theorems/d5gq/apsp b1_s16_long.edges 11 5                                  # RESULT VALID d=11 D=5 n=5600

Interpretation: at q = 7 one arc takes s = 16 (4% of the 400 points), two arcs 8 + 8 (2% per arc, 4% in total), and four
arcs 4 + 4 + 4 + 4 (1% per arc, 4% in total) were reached. These are not optimized maxima: the step budget at s = 24 (one
arc) and s = 8 (four arcs) was 9000 steps, so those are lower bounds for the limits.
