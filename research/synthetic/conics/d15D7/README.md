# (15,7): the same freed sets in the seven-copy layout, with a PSL(2,31) hub graph

Job "conics" (research/synthetic/CONICS.md, Section 3.4). The seven-copy layout of the lab's earlier (15,7) candidate
(research/cell147/typedmirror/README.md: types H H D H H D D, three matchings per copy, the mirrored local duality on 768
points on the nine non-friendly transitions; typed input research/frontier/sols/d15D7_hex11_typed133_K62_n2497075.sol)
with the friendly freed sets of the (14,7) build (research/synthetic/conics/d14D7/README.md):

- R_H = the 15,984 points of the Hermitian spread of H(11) (a segment set);
- R_L = the 132 lines meeting v = <e1, e6> plus the exact whisker set of POLISHED.md Theorem 6.5 (14,652 lines; a dual
  segment set).

Free slots per copy: A [17520, 17520, 30072, 32736, 32736, 30072, 30072], B [30072, 30072, 32736, 16188, 16188, 32736,
32736]. The hub graph may have degree at most 15 - 7 = 8; a random one with 16,188 hubs per side leaves 110,476 same-side
pairs beyond distance 6, so we use the Haar graph of PSL(2,31) (14,880 elements) with 8 generators S chosen by local
search so that (S S^-1)^3 = (S^-1 S)^3 = PSL(2,31): line-side hub x ~ point-side hub x s. Then every two hubs of the same
side are within 6 in the hub graph alone, and

    n = 14 * 177,156 + 2 * 14,880 = 2,509,944   (lab 2,501,491; table 2,480,184).

Files: psl_hubgraph.py (the hub graph, written to hub_psl31.txt: first line K, then "a b" per edge); the graph is built
with ../d14D7/tm_build_herm.py (HUBGRAPH=hub_psl31.txt ... make ...), solution
research/frontier/sols/d15D7_hex11_typedwhisk_n2509944.sol; checks/ has the all-pairs check.
