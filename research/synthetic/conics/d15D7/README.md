# (15,7): the same freed sets in the seven-copy layout, with a PSL(2,29) hub graph

Job "conics" (research/synthetic/CONICS.md, Section 3.4). The seven-copy layout of the lab's earlier (15,7) candidate
(research/cell147/typedmirror/README.md: types H H D H H D D, three matchings per copy, the mirrored local duality on 768
points on the nine non-friendly transitions; typed input research/frontier/sols/d15D7_hex11_typed133_K62_n2497075.sol)
with the friendly freed sets of the (14,7) build (research/synthetic/conics/d14D7/README.md):

- R_H = the 15,984 points of the Hermitian spread of H(11) (a segment set);
- R_L = the 132 lines meeting v = <e1, e6> plus the exact whisker set of POLISHED.md Theorem 6.5 (14,652 lines; a dual
  segment set).

Free slots per copy: A [17520, 17520, 30072, 32736, 32736, 30072, 30072], B [30072, 30072, 32736, 16188, 16188, 32736,
32736]. The hub graph may have degree at most 15 - 7 = 8; a random one with 16,188 hubs per side leaves 110,476 same-side
pairs beyond distance 6. So we use a Haar graph: hubs on both sides indexed by G = PSL(2,29) (12,180 elements),
line-side hub x joined to point-side hub x s for s in a set S of 8 elements, with S chosen by local search so that
(S S^-1)^3 = (S^-1 S)^3 = G. Then every two hubs of the same side are within distance 6 in the hub graph alone, and

    n = 14 * 177,156 + 2 * 12,180 = 2,504,544   (lab 2,501,491; table 2,480,184).

The slots allow up to 17,520 line-side and 16,188 point-side hubs (n = 2,513,892) with a better hub graph. The same search over PSL(2,31) (14,880
elements, n would be 2,509,944) reached 14,879 of 14,880 and stalled; psl31_search.log is that run.

Files:
- psl_hubgraph2.py: the hub graph search (`python psl_hubgraph2.py 29 1 hub_psl29.txt`, seed 1); output is K on the first
  line, then one edge "a b" per line (line-side hub a, point-side hub b, both in 0..K-1).
- hub_psl29.txt, psl29_search.log: the hub graph used and its search log.
- Build: from research/frontier/sols,
  `HUBGRAPH=<repo>/research/synthetic/conics/d15D7/hub_psl29.txt python <repo>/research/synthetic/conics/d14D7/tm_build_herm.py make <repo>/research/p4/d6/hex/hex_q11.bin d15D7_hex11_typed133_K62_n2497075.sol d14D7_hex11_mirror768_n1774632.sol 1 d15D7_hex11_typedwhisk_n2504544.sol out.edges`
  gives n = 2,504,544, 18,678,612 edges, degrees 12 to 15.
- Solution: research/frontier/sols/d15D7_hex11_typedwhisk_n2504544.sol.
- checks/: the all-pairs check (research/lifts/coordinator_check/apsp_mt.c on the built edge list).
