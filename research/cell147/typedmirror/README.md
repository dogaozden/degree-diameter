# Typed levels plus mirrored surgery: (14,7) 1,789,588 (job cell-14-7, 2026-10-25)

Two constructions combined:

- **Typed levels** (cell-16-7 session, research/squads/cells/d16D7.md): five copies of the incidence graph of H(11) with
  types H D H D H and two matchings per level (j -> j+1, j -> j+2). On the six *friendly* transitions (H -> D or
  D -> H) the matching is the identity, and any non-collinear point set R_H or non-concurrent line set R_L can be freed.
  Master's (14,7) 1,788,052 = 10·177,156 + 2·8,246 uses |R_H| = 8,645 and |R_L| = 8,246 (orbits of an order-133
  collineation) and does no surgery on the four *non-friendly* transitions 4->0, 0->2, 2->4 (H -> H) and 1->3 (D -> D).
- **Mirrored surgery** (this job, research/cell147/mirror/ and research/theorems/MIRRORED_SURGERY.md): a bijection sigma
  from points to lines and a 768-point set R' (the 756-point W(E7) orbit plus 12 extra points) with R' non-collinear,
  sigma(R') non-concurrent and sigma(Gamma_2(x)) = Gamma_2(sigma(x)) for every x in R'. This is exactly (H1)-(H3) of
  the one-transition surgery theorem in d16D7.md, for any H -> H transition with matching sigma, and (dually) for a
  D -> D transition with matching sigma^-1 and freed lines sigma(R').

So the four non-friendly transitions get sigma (H -> H) or sigma^-1 (D -> D) and free 768 elements each. Free slots
per level (A = outgoing, B = incoming):

| level | type | free A-slots | free B-slots |
|---|---|---|---|
| 0 | H | R_H (0->1) + 768 (0->2) = 9,413 | 768 (4->0) + R_L (3->0) = 9,014 |
| 1 | D | R_L (1->2) + 768 (1->3) = 9,014 | R_H (0->1) + R_H (4->1) = 17,290 |
| 2 | H | R_H (2->3) + 768 (2->4) = 9,413 | R_L (1->2) + 768 (0->2) = 9,014 |
| 3 | D | R_L (3->4) + R_L (3->0) = 16,492 | R_H (2->3) + 768 (1->3) = 9,413 |
| 4 | H | 768 (4->0) + R_H (4->1) = 9,413 | R_L (3->4) + 768 (2->4) = 9,014 |

Each side gets K = min = |R_L| + 768 = 9,014 hubs (one free slot in every level, 5 edges), so

    n = 10·177,156 + 2·(8,246 + 768) = 1,789,588   (master 1,788,052, +1,536; table 1,771,560).

The hub graph (degree <= 9 = 14 - 5) is 9 random perfect matchings between the two hub sides; all same-side hub
distances are <= 6 (checked with bitsets in tm_build.py). The surgeries on different transitions are independent (each
proof uses only its own two levels), so the diameter argument is the one of d16D7.md, transition by transition.
The graph has no symmetry left (the order-133 collineation does not preserve R'), so the check is a plain all-pairs
bit-parallel BFS (apsp_mt, 1,789,588 sources): checks/d14D7_hex11_typedmirror768_n1789588.check.txt.

## (15,7): 2,499,748 (candidate; spot check only)

Master's (15,7) 2,497,075 has seven levels H H D H H D D, three matchings and nine non-friendly transitions (0->1,
0->3, 1->3, 1->4, 3->4, 4->0 are H -> H; 2->5, 5->6, 6->2 are D -> D). Freeing the 768 mirrored elements on all nine
gives free A-slots [R_H + 1,536, R_H + 1,536, 2R_L + 768, 2R_H + 768, 2R_H + 768, 2R_L + 768, 2R_L + 768] and B-slots
[2R_L + 768, 2R_L + 768, 2R_H + 768, R_L + 1,536, R_L + 1,536, 2R_H + 768, 2R_H + 768], so up to 10,181 line-side and
9,782 point-side hubs. The hub degree is only 15 - 7 = 8, and a random bipartite graph with unequal sides (line-side
degree about 7.7) leaves hundreds of same-side pairs beyond 6. So both sides get 9,782 hubs. Random degree-8
matchings still leave 70-90 pairs beyond 6 (seed 1: 76), and 73 degree-preserving 2-switches aimed at those pairs
remove them.
That gives n = 14·177,156 + 2·9,782 = **2,499,748** (+2,673).
Solution research/frontier/sols/d15D7_hex11_typedmirror768_n2499748.sol (rebuild byte-identical). Without symmetry a
plain all-pairs check of 2.5M vertices takes about 8 core-hours, which did not fit in this session: see
checks/d15D7_hex11_typedmirror768_n2499748.check.txt for the hypothesis checks and the BFS from all 19,564 hubs
(max eccentricity 7), which together with the theorem covers every pair.

## Files

- tm_build.py: builds the edge list (typed5s vertex numbering) from master's typed .sol and the mirrored .sol, re-checks
  every hypothesis (R_H non-collinear, R_L non-concurrent, R' non-collinear, sigma(R') non-concurrent, local duality at
  all 768 points), the hub graph distances and the degrees. `make` also writes the solution file.
- apsp_src.c: apsp_mt.c restricted to a list of sources (spot checks only).
- checks/: check files.

Solution: research/frontier/sols/d14D7_hex11_typedmirror768_n1789588.sol (names the two input .sol files with their
sha256, then the hub graph edges). Rebuild and check:

```
cc -O2 -o hexgen2 research/d13D7/hexgen2.c -lm && ./hexgen2 11          # hex_q11.bin (sha256 e60db369...)
python3 research/cell147/typedmirror/tm_build.py build hex_q11.bin research/frontier/sols/d14D7_hex11_typedmirror768_n1789588.sol g.edges
cc -O2 -pthread -o apsp_mt research/lifts/coordinator_check/apsp_mt.c && ./apsp_mt g.edges 14 7 4
```

## Next steps

K is set by the line sets: |R_L| + 768 on four of the ten slot counts. Larger non-concurrent line sets (no G-invariance
is needed any more) raise n by 2 per line until |R_L| reaches |R_H| = 8,645 (then both sets must grow). Master's R_L and
R_H are already maximal (no line can be added to R_L, no point to R_H; checked here), so this needs exchange moves
(local search on 177,156 elements), not a greedy completion. For (16,7) (q = 13) the 813-point mirrored set would
replace the 2 orbits (122 elements) freed on the non-friendly transitions now (about +1,382), but without a common
symmetry the plain check of 4M vertices costs about 44 core-hours.
