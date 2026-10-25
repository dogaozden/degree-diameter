# raise-d4D10: notes (Haiku worker, job "raise2-4-10", round 2)

Goal: beat 12,416 at (Δ, D) = (4, 10). Table 11,748 (Loz); Moore bipartite 59,048.
Record: Haar graph of Z97 ⋊19 Z64, N = 6208, n = 12,416 (voltage-lifts branch, research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt).

## Round 1 (branch claude/raise-d4d10-haar-l3s318; its notes are at that branch's research/squads/cells/raise-d4D10.md)
- About 150 anneals of 300 s over N = 6209–6560 (metacyclic, n = 1) plus 4 long re-anneals. No solve.
- Closest: N = 6216 meta 259 24 97 (cost 1, stalled to 2400 s); N = 6394 meta 278 23 45 and meta 139 46 6 (cost 1, one 300 s seed each).
- Untried by round 1, and taken up here: non-metabelian families; and metacyclic × Z_n with n ≥ 2 (see below).

## Round 2 (this branch)
Gap found: research/frontier/sizelaw/small_cands.py only generates metacyclic Z_m ⋊ Z_k with n = 1. The product
metacyclic × Z_n (n ≥ 2, order m·k·n) is a haar_gen3 family ("meta m k r n") that no earlier sweep screened.
- Candidates for N = 6209–6330: 5,227 meta × Z_n (n ≥ 2) + 2,571 metacyclic (n = 1) + 37 matrix/product families (cands_gen.py).
  Tools in tools/: gen_meta_xn.py (the new family), screen_all.py (RANDSAMPLE 200, same call as haar_cell.py), rank.py (same
  score as haar_cell.py: (p10 + median) / mu(N)). screen_6209_6330.tsv holds all 7,835 screens.
- Record screen score (N = 6208): 4.03. Candidates scoring below 4 in the window: about 40.
- Batch 1 (queue1.txt): top 40 overall plus 20 more with n ≥ 2, 300 s each, seed 1, 4 cores, THREADS=1, nice.
  Round-1 near misses excluded (N = 6216 meta 259 24 97, 6270 meta 209 30 26, 6270 meta 418 15 49, 6275 meta 251 25 4,
  6321 meta 301 21 23).
