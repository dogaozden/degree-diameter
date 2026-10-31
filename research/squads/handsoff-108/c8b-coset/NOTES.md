# c8b-coset (handsoff-108): notes

Worker: c8b-coset. Seeds 108951-108999 (plan). Family: bipartite coset graphs over PSL(2,181), H = C5 (split torus),
D = union of two regular double cosets H g H (degree 10), N = 592,956 per side.

## Plan (started 22:12 UTC)
1. Fast exact cost (fastc.c): labels of cosets by an arithmetic invariant, bottom-up/top-down BFS.
2. Validate against coset2 output (c8-wild/psl181_h5R2_60.tsv, 60 candidates, exact match of uncB/uncA).
3. Anneal over pairs of double cosets (F15W3-style schedule), report chain minima in units of 5.
