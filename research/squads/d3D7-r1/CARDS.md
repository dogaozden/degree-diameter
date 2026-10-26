# Squad d3D7, round 1 cards (Oct 26 2026). Shared brief: BRIEF.md

- c1 medium groups, medium bases (salift breadth): every group of order 11, 13, 15, 16, 14, 12 at the p giving
  n = 176 (N=11,p=8), 182 (13,7), 180 (15,6), 192 (16,6 and 12,8), 196 (14,7); several seeds; smallest n first.
- c2 small groups, big bases: build a better annealer (tabu / parallel tempering / smoothed cost with distance-8 term /
  targeted moves); must first hit cost 0 on the calibration C7 p=12 (n=168); then Z5 p=17 (170), order 8 p=11 (176),
  order 9/10 p=10/9 (180).
- c3 surgery on the record (unstructured): insert vertex pairs into Conder's 168 by edge-pair gadgets (+2, +4), then
  low-temperature local search (sa3-style) from that seed, moves restricted near the defect first.
- c4 quotient growth: quotient Conder's graph by a subgroup H of C2 × (C7 ⋊ C3) (H = C2, C3, C6, C7, C14, C21), insert
  one vertex pair into the quotient base with a gadget, re-lift over H and anneal from there (n = 168 + 2|H|).
- c5 extra-symmetry lifts (orbit-search analogue): voltage assignments invariant under a base automorphism σ paired with
  a group automorphism φ; shrinks the space so p = 6..9 bases over groups of order 10..21 can be searched deeper.
- c6 coset graphs with point stabilisers (non-semiregular): G of order n acting on each side with stabiliser of order 2
  (vertices G/H1 ∪ G/H2, edges from double cosets H1 g H2); groups of order 170..200 in GAP. Not covered before.
- c7 tree completion (cage style): fix the depth-5 Moore tree around an edge (126 vertices) + extra vertices; anneal
  only the remaining edges, keeping girth ≥ 10.
- c8 algebraic graphs: Lazebnik–Ustimenko-type and polynomial incidence graphs over GF(3), Z_m and small rings; check
  the 162-vertex VT diameter-7 graph's structure and look for 170–200-vertex relatives.
- c9 wildcard: an approach none of c1–c8 uses.
- c10 wildcard: an approach none of c1–c9 uses (exact methods: SAT / ILP / orderly generation under a symmetry).
