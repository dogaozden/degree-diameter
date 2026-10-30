# Round bh5b-r2 (job beyond-haar-d5b, Oct 30 2026, ~04:45 UTC)

Context: the exact searches found (5,5) graphs on 384 vertices (lifts of 2+2 bases by groups of order 96 = 2^5 x 3,
many groups with solutions), and dcenum's annealer is 4.6x faster after a bug fix (round 1, c1).

- c1 (7,5): fixed annealer on the previous job's non-solvable near misses SmallGroup(1260, 61/62), (1320, 133..138), |H| = 2.
- c2 (7,5): fixed annealer on |H| = 3 near misses SmallGroup(1806, 15), (1830, 2), (1806, 2), then orders 1848-1866.
- c3 (7,5): |H| = 2 sweep from the top: orders 1318, 1316, 1314, ... downward (the main queue goes upward from 1214).
- c4 (7,5): 2+2 lifts over 2-rich groups of order 304, 312, 320 (large Aut), bases [[1,6],[6,1]], [[2,5],[5,2]], [[3,4],[4,3]].
- c5 (6,5): 2+2 lifts over 2-rich groups of order 176 and 192, bases [[1,5],[5,1]], [[2,4],[4,2]], [[3,3],[3,3]].
- c6 (8,5): 2+2 lifts over 2-rich groups of order 520, 528, 544 (and 516), bases [[1,7],[7,1]] .. [[4,4],[4,4]].
- c7 (5,5) > 384: 3+3 bases lifted by 2-groups / 2-rich groups of order 64-72 with long anneals and all 10 3+3 bases.
- c8 wildcard: an approach none of c1..c7 uses, for (5,5) > 384, (6,5) > 684, (7,5) > 1,200 or (8,5) > 2,048.
