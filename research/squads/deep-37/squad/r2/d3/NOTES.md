# d3 (round 2): non-symmetric exact LNS from structured starts

Tool: squad/r1/c6 lns.c (copy in d3/lns.c, binary d3/lns, group d3/grp_id170.txt = trivial group). Each step removes
8-12 edges near a random far pair, enumerates all completions (pruned by a far supergraph bound, exact for far <= threshold),
accepts a uniform random completion with far <= max(cur, best + DELTA). Chunks of about 80 s, trivial group.

Start (score37 at start) -> final far after my chunks:
- fresh56 r3b second far-60 graph (60) -> 43 after 2 chunks (5 s into chunk 2). Same isomorphism class as round-1 far-43 (iso.py).
- r3e_c2r_far59 (59) -> 59. Two chunks and a band-4 walk (60 s): no move.
- r3a_far90 (90) -> 86. Stuck in chunk 2; radius-3 k 10-13 no move; band-8 walk moved to 93, a plateau descent returned to 86.
- c5_far78 (78) -> 78. Chunk 2 and band-6 walk: no move.
- c6_polarity_z5 (80) -> 80. One chunk, no move.
- r3c_C5_far65 (65) -> 65. Two chunks, no move.
- r3a_far115 (115) -> 115. One chunk, no move. Unpruned k=4 check: identity is the only completion with far <= 115.
- c4_A4f6_far132 (132) -> 132. One chunk, no move.
- r3b_F20_far160 (160) -> 160. One chunk, no move.
- From far 43 (fresh56 chain): k=13..14 regions exhausted (only identity); k=15..18 regions hit the 10 s cap
  (bound too weak), no move.

Validation: pruned search vs unpruned on the far-115 start: 30771 unpruned regions (k=4) all band 1; 5 pruned regions with
band 2 confirmed by Python brute force (min far 115).

Conclusion: no start beat 43. The fresh56 start (60) reached the 43 basin. The r3a far-90 start settled at 86. The other starts stayed at their start value. Starts with far 115-160 are rigid under k<=12 exact repair. A tighter lower bound for k>=15 was not found in time.
