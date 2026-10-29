# (16,7): the same freed sets at q = 13, n = 4,081,072

Job "conics" (research/synthetic/CONICS.md, Section 3.4). Five copies of the incidence graph of H(13), types H D H D H,
two matchings per copy (the layout of the lab's 4,052,108, research/squads/cells/d16D7/), with:

- friendly transitions: the identity, freeing R_H = the 30,772 points of the Hermitian spread (the lines of H(13) in
  the elliptic hyperplane x0 + 2 x4 = 0; a segment set) and R_L = the 182 lines meeting v = <e1, e6> plus the exact
  whisker set of POLISHED.md Theorem 6.5 with c = 2, (c0, c1) = (1, 1) (28,392 lines; 28,574 in all, a dual segment set);
- non-friendly transitions: the mirrored local duality sigma on 792 points of the lab's q = 13 mirror solution
  research/frontier/sols/d16D7_hex13_R792_n4025508.sol (instead of the 122-point surgery of the 4,052,108 record);
- 29,366 hubs per side (the smallest free count, 28,574 + 792), joined by 11 seeded random perfect matchings (seed 1;
  no same-side pair beyond distance 6 at the first try).

    n = 10 * 402,234 + 2 * 29,366 = 4,081,072   (lab 4,052,108; table 4,022,340).

Builder: research/synthetic/conics/d14D7/tm_build_herm.py (q = 11 and q = 13); from research/frontier/sols,

    python3 ../../synthetic/conics/d14D7/tm_build_herm.py build ../../p4/d6/hex/hex_q13.bin d16D7_hex13_typedwhisk_n4081072.sol g.edges

re-checks every hypothesis (segment set, dual segment set, exact whiskers, the 792-point local duality, hub distances,
degrees 14..16) and writes the edge list, sha256 350f9e078ebcc2e3bd997cb4fafce94f074da937f02cef59f91a14e5369e476c
(byte-identical to the edge list written by `make`). hex_q13.bin sha256 57aa5dfc... as in the record's check file.
The typed input d16D7_hex13_typed61_K244_n4052108.sol supplies only the layout (types and levels); its freed sets are
replaced. hexsets.py: the sets of H(13) and their orbit counts under the torus.

checks/: the all-pairs check (apsp_fast.c, split over source ranges).
