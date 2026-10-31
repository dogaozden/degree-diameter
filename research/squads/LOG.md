# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## Round sdhi-r1 (Oct 31 2026, 06:53-07:15 UTC, job selfdual-hi, session claude/selfdual-haar-d7-d8-rwwjp8)

Goal: self-dual (bipartite Cayley) Haar graphs above (5,8) 9,760, (5,7) 3,120, (6,8) 31,680, (7,8) 95,760. Cards in
`sdhi-r1/cards.md`, scorer `research/selfdual-hi/src/sdhi` (full BFS on every SOL), scoreboard `sdhi-r1/scoreboard.jsonl`.
The box ran about 20 processes on 4 cores, so most cards cut their per-type time to 2-8 s.

| card | direction | best (uncovered) | at |
|---|---|---|---|
| c1 | (5,8) metacyclic C_p:C_k, p prime (8 groups) | 9 | C181:C27, N = 4,887 (no scoreboard line: stopped at the box) |
| c2 | (5,8) composite metacyclic, <= 1 involution (8 of 181 groups) | 15 | C993:C5, N = 4,965 |
| c3 | (5,8) Q x H products (13 groups) | 13 | PSL(2,7) x Z30, N = 5,040 |
| c4 | (5,8) deep tabu on the record shape C61:C_k, C41:C120, .. | 16 | C41:C120, N = 4,920 (C61:C80 itself: 6, but N = 4,880 is the record order) |
| c5 | (6,8) haar_sd self-dual vs orbit k = 3 | sd 10 at PSL(2,11) x Z25 (orbit k=3 fails there: 11,234, Z25 has no unit of order 3); SL(2,7) x Z49: orbit 3, sd 40 | N = 16,500 / 16,464 (no scoreboard line) |
| c6 | (7,8) haar_sd psi = inversion with e in S | 3,268 | the structural trap (double cover with a perfect matching), as the card warned; plain orbit 20 on the record group |
| c7 | wildcard: psi of order 2 and 6 on Q x small dihedral at (5,7) | 12 | SL(2,5) x D7, N = 1,680 (no scoreboard line) |
| c8 | (5,7) metacyclic C_p:C_k (6 groups) | 34 | C11:C145, N = 1,595 (no scoreboard line) |

No card found a valid graph above a record. Kept: nothing from the cards directly. The round confirmed, across five
families, that self-dual sets lose to plain or orbit-symmetric sets at D = 7, 8 in groups with a large cyclic factor or
a small non-abelian part. That led to the word-collision analysis (`research/selfdual-hi/README.md`): self-dual
families have extra commutation coincidences, at a rate set by the commuting probability of G. What I did next: (5,8)
on SL(2,17), PGL(2,17), PSL(2,17) x Z2 (order 4,896, just above the record, commuting probability 0.4 %), where the
best self-dual family keeps 98 % of the distinct words; there plain annealing reached 3-4 and self-dual 6-7 uncovered
in the first minutes. Honest note: the squad added breadth and negative results, no new idea that changed the
direction; the useful direction came from my own diagnostics while it ran.
