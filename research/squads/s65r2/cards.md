# Round s65r2 cards (goal: bipartite (6,5) graph on > 684 vertices)

Shared context, scorer, rules: CONTEXT.md (new section at the end: Haar graphs in disguise, SKIPHAAR).
Evolved from s65r1: the coset family is the only one whose best costs (6-8) came near, but those hits were Haar graphs
of excluded groups; round 2 sweeps the genuinely non-Haar coset graphs (the family of the vertex-transitive (5,5) 384
graph) at the next orders, and finishes the exhaustive Haar search at 352-360.

- **c1 non-Haar |H| = 2 cosets, order 704, ids 1-693.** SKIPHAAR export in chunks, all (H, K) pairs, SA 3 s, then
  re-anneal the best 5 for 120 s.
- **c2 same, order 704, ids 694-1387.**
- **c3 same, orders 706-718 (51 groups) and 720 (840 groups).**
- **c4 non-Haar |H| = 3 cosets, orders 1035-1077 (|G| = 3N/2, N = 690-718 vertices), all groups except 1044, 1056.**
- **c5 non-Haar |H| = 3 cosets, order 1080 (583 groups, 720 vertices).**
- **c6 non-Haar |H| = 4 cosets (C4 and V4), orders 1372-1436 with few groups (N = 686-718).**
- **c7 exhaustive Haar search (haarex2), the 69 low-involution groups of order 352-360 never run** (list
  research/s65/haar/remaining.txt, in order).
- **c8 mcos multi-orbit coset graphs** (G regular on one side, other side G/K1 u G/K2 etc.), orders 352-360 and the
  lift-like types at |G| = 172-180.
