# w5 notes (handsoff-49): lifts of small 4-regular bipartite bases over groups

Start: 2026-10-31 21:41 UTC. Planned end: 23:41 UTC (2 hours).

## Setup
- `gen_bases.py`: random and named bases (k55m, Q4, Fano complement, circulants, random multigraphs).
- `gen_matrix_bases.py H`: ALL connected 4-regular bipartite multigraphs on H+H vertices (matrix M, row/col sums 4):
  H=2: 2 bases, H=3: 6 bases (bases/mh3_*.txt), H=4: 31 bases.
- `gen_meta.py lo hi`: metacyclic groups meta:m:k:r of order lo..hi with r^k = 1 mod m (validated).
- `screen.py SECS OUT.tsv BASES GROUPS SEED`: runs `tools/flift` (d=4, D=9) for SECS per (base, group) pair.
- Always check a meta spec: r^k = 1 mod m. An invalid one (e.g. meta:17:36:2) gives a fake cost 0 that apsp rejects.
  I hit that once (apsp said diameter 10); the verified valid lift is w5/out/chk_b6x_612.edges (n=3672, VALID).

## Findings so far
- Haar base (h=1, 4 parallel edges) reaches cost 0 at N=2485 in ~2 s (calibration, flift is fine).
- h=5..8 bases (the card's 10..16 vertices) over orders 312..500: cost stays ~100-150 after 60 s (stuck). Poor.
- Small multi-edge bases do much better: h=3 base over N=612 (n=3672) gives cost 0 quickly, verified VALID by apsp
  (not a record, n < 4970). For N=832 (n=4992) the best h=3 bases give costs 30-60 in 3 s.
- Card deviation: the squad goal is a record, so I also work the h=3 and h=4 families (bases 3+3 and 4+4, multigraphs
  allowed), which are smaller than the card's 5+5..8+8. Reason: data above.

## Screens (flift SA, d=4 D=9; cost = unreached (root, vertex) pairs summed over base roots; 0 = valid)
- h=3, 6 bases (bases/mh3_*.txt, doubled C6 = mh3_3 is the best), N=832 (n=4992), 3 s: costs 30-60
  (results_h3_832.tsv). 40 s: mh3_3 + meta:13:64:8 -> 34 (results_h3_832_long.tsv).
- h=3 threshold (mh3_3/mh3_4, 10 s): N=700 cost 8-12, N=748 16-18, N=780 20-24, N=832 30-50. N=612 cost 0 in 1 s.
- h=4, 31 bases (bases/mh4_*.txt) at N=624 (n=4992), 3 s, 3 groups: best costs 40-60 (results_h4_624.tsv).
- Dipole/Haar (h=1) is the outlier: cost 0 at n=4970 in ~2 s. The walk-count ratio (~3.94 same-side walks per target)
  is the same for every h at fixed n, so the gap is in the landscape, not the counting.
- The card's h=5..8 bases over N=311..500: cost 100-150 after 60 s (stuck), worst family tested.
