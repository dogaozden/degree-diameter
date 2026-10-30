# Round s65r5 cards (goal: bipartite (6,5) graph on > 684 vertices)

Shared context: CONTEXT.md (see "New after round s65r4"). Evolved from s65r4: the director calibrated the search that
found the vertex-transitive (5,5) record (C3 x P128, non-Haar |H| = 2 bi-coset graphs: one lone cost-0 outlier among 231
pairs) and this round runs its (6,5) analogue over all 4,284 groups P of order 256 with at most 11 involutions
(768 vertices), plus the remainder of the exhaustive Haar search and the semidirect variants.

- **c1-c6 C3 x P256 sweep**: ids research/s65/c3p256/part_00 .. part_05 (one part per card); export in chunks of 50
  (c3p_export.g, non-Haar pairs only), anneal every pair 3 s, re-anneal the best 3 for 60 s.
- **c7 Haar exhaustive remainder**: groups of research/s65/haar/remaining_r4.txt and next_361_380.txt with no DONE log
  yet (see round-4 folders).
- **c8 C3 : P256 (semidirect, P acting on C3 by inversion through an index-2 subgroup)** for the 158 groups P with 1 or
  3 involutions, same pipeline.
