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

## Update 22:50 UTC: tabu search and the h=2 family
- `tabu.c` = tools/flift.c plus env TABU=1: full-neighbourhood tabu search (best non-tabu move each step, tenure 12,
  kick after 300 steps). Use: `TABU=1 ./tabu BASE GROUP 4 9 SECS SEED 8 OUT`. Tabu beats SA on the h=3/h=4 pairs.
- Cost unit: flift cost = unreached (root, base vertex, group element) triples; far pairs = cost * N / 2 (score48 agrees).
- BEST NEAR MISS (n = 4992, h=2 base mh2_1 = [[2,2],[2,2]], i.e. K22 with every edge doubled, group meta:13:96:5):
  cost 4 (seed 31 in 50 s and seed 61 with meta:39:32:31). Files: out/t_mh2_1_1248_s31.edges (verified: far=2496,
  INVALID). Not a record. In both cost-4 states the unreached triples are same-side pairs only:
  (root 1, v 1) x2, (root 2, v 3), (root 3, v 2), and the group elements lie in the index-4 normal subgroup
  {j = 0 mod 4} (quotient Z_4 of the abelianisation). Suspect a Z_4-parity obstruction from the base.
- h=2 seeds at 50 s: typical 10-14, best 4. Groups of order 1248 screened (25 s): meta:26:48:3 10,
  meta:39:32:31 4-12, meta:156:8:5 14, agl1 13 x cyc 8 21, sl2 3 x meta 13 4 5 16, S4 x Z52 25. Many others 46-5000.
- h=3 mh3_3 x meta:104:8:31 (N=832, n=4992): best cost 19 (out/t_mh3_3_104_8_31_s41.edges, INVALID).
- h=4 mh4_14 x meta:39:16:5 (N=624): cost 32 at 55 s.
- Scoreboard lines written: cost 22 (h=3, n=4992), cost 19 (h=3), cost 4 (h=2, n=4992).

## Haar-family note for the coordinator
- A base with a semiregular automorphism group Z_h and voltages constant on its orbits is a Haar graph of G x Z_h
  (bi-circulant base K44 -> Haar over G x Z_4). Those lifts are inside the w1/w2 domain.
