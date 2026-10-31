# six-five-384: Haar graphs of degree 6 and diameter 5 on 768 vertices (Oct 31, 2026)

Goal: a bipartite graph of maximum degree 6 and diameter 5 on more than 684 vertices (table value 684). Earlier jobs
(branch claude/squad-6-5-rounds-ts5nxk, research/s65/README.md) closed every degree-6 Haar graph on 686-800 vertices
except order 384 (20,169 groups, 768 vertices). This job closes order 384.

Work in progress; this file is updated as the run proceeds.

## Setup

- GAP 4 from pip (`pip install passagemath-gap`, which bundles the SmallGroups data); run as
  `site-packages/gap/gap -l site-packages/gap -A` (`-A`: the bundled ctbllib has no data and breaks autoloading).
- `src/inv384.g`: invariants of all 20,169 groups (`data/inv384.txt`: abelian invariants, r2 = rank of G/G'G^2,
  involutions, |Z|, normal Sylow 3, IdGroup of G/O_3(G), derived length).
- `src/hx_export_batch.g`, `src/hx_export_any.g`: multiplication table + Aut(G) generators, haarex format.
- `src/haarex4.c`: research/s65/tools/haarex3.c with faster per-prefix work (same enumeration; output identical to
  haarex3 on 342_12, 360_53 and 6 order-384 groups; finds the 684 record's 10 VALID sets on 342_12).
- `src/qfeas.c`: quotient counting test (below).

## Filters (exact)

H(G,S) has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Every element of G is then the value of one of the 781
non-backtracking words of length 0, 2, 4 on each side.

1. **Rank.** If G/G'G^2 = C2^r with r >= 5: the image of (S^-1 S)^2 in C2^r consists of sums of even subsets of size
   <= 4 of the 6 images, at most 1 + 15 + 15 = 31 < 32 elements. Excludes 1,842 groups (r2 = 5: 1,806; 6: 34; 7: 2).
2. **Quotient counting** (`src/qfeas.c`). For N normal, Q = G/N, every coset needs >= |N| of the 781 words, on both
   sides, for some image 6-tuple (q_1 = e, q_2 up to Aut(Q)). Results: order 32 (T = 12): only C2^5 fails; order 48
   (T = 8): none fails; order 64 (T = 6): 64_193, 64_194, 64_202 fail (best min 5) besides the rank-5/6 groups
   64_260-267. 135 of the order-128 groups G/O_3(G) have one of 64_193/194/202 as a quotient by a central C2, which
   excludes 923 order-384 groups with r2 <= 4.
