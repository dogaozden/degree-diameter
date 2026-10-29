# (14,7): the largest freed sets of Theorem B, from the Hermitian spread and the exact whiskers of Theorem D

Job "conics" (research/synthetic/CONICS.md, Section 3.4). The five-level layout HDHDH of H(11) of the (14,7) record
(research/cell147/typedmirror/: 1,789,588 = 10*177,156 + 2*(8,246 + 768)) with larger friendly freed sets:

- R_H = the 15,984 points of the Hermitian spread of H(11) (the 1,332 lines of H(11) in the elliptic hyperplane
  x4 = -x0): a segment set, the largest possible (D7_HEXAGON.md Proposition 1.4). D7_HEXAGON.md Remark 9.4 proposed it.
- R_L = the 132 lines meeting the spread line v = <e1, e6> (other than v) and the exact whisker set W of
  POLISHED.md Theorem 6.5 relative to the same spread and v (14,520 lines): 14,652 lines. Two of these lines meet only
  in a point of the spread hyperplane, which is the only such point on each line, so R_L is a dual segment set
  (computed and checked in whiskers_exact.py and again in the builder).

Theorem B of D7_HEXAGON.md repairs a friendly transition for any segment set; the non-friendly transitions keep the
mirrored local duality on 768 points. Free slots per level: A [16752, 15420, 16752, 29304, 16752],
B [15420, 31968, 15420, 16752, 15420], so 15,420 hubs per side and

    n = 10 * 177,156 + 2 * (14,652 + 768) = 1,802,400   (record 1,789,588; table 1,771,560).

Hub graph: 9 seeded random perfect matchings (seed 1); all same-side hub distances <= 6 (checked in the builder).

Files:
- tm_build_herm.py: research/cell147/typedmirror/tm_build.py with these freed sets (computed inside) and segment-set
  checks. `make HEX TYPED_SOL MIRROR_SOL SEED OUT.sol OUT.edges` and `build HEX SOL OUT.edges` (SOL names the two inputs
  with their sha256). Option --pencils: the Remark 9.4 version (R_L = the 9,072 lines through 756 pairwise opposite
  points, optionally plus extra lines): 1,791,240.
- research/frontier/sols/d14D7_hex11_typedwhisk_n1802400.sol: the solution (next to its two inputs, as `build` expects) (inputs by name and sha256, hub counts, hub graph).
- whiskers_exact.py: the exact whisker set and R_L on their own; score_RL.py: dual segment set checker.
- extend_RL.py, extra_lines.txt, R0_756.txt: the intermediate pencil version (1,442 extra lines, 1,794,124; superseded).
- checks/: the all-pairs check.
Inputs: research/p4/d6/hex/hex_q11.bin (sha256 e60db369...; the file of the 1,789,588 check),
research/frontier/sols/d14D7_hex11_typed133_K62_n1788052.sol, research/frontier/sols/d14D7_hex11_mirror768_n1774632.sol.
