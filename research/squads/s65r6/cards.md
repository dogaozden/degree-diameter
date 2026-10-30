# Round s65r6 cards (goal: bipartite (6,5) graph on > 684 vertices)

Shared context: CONTEXT.md ("New after round s65r5"). Round 5 closed the exhaustive Haar search for all 93 groups of
order 352-360 with <= 3 involutions (none works) and half of the C3 x P256 sweep (best 48 of 768). This round finishes
the C3 x P256 sweep, starts P256 with 12-15 involutions, finishes the slow Haar groups of order 361-380, and runs
non-Haar |H| = 2 bi-coset sweeps at the next orders (722-760) and the rest of 720.

- **c1-c3 C3 x P256 (<= 11 involutions), remainder**: research/s65/c3p256/r6_a.txt, r6_b.txt, r6_c.txt.
- **c4 C3 x P256 with 12-15 involutions**: research/s65/c3p256/r6_d.txt (first 400 of 2,000+).
- **c5 exhaustive Haar, the 11 slow groups of order 361-380** not yet run.
- **c6 non-Haar |H| = 2 bi-coset sweep, orders 722-740**; **c7 orders 742-760**; **c8 order 720, ids 451-840**.
