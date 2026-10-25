# raise-d4D10: notes (Haiku worker, job "raise-4-10")

Goal: beat 12,416 at (Δ, D) = (4, 10). Table 11,748 (Loz); Moore bipartite 59,048.
Current record: Haar graph of Z97 ⋊19 Z64, N = 6208 (connection set (0,0), (74,51), (30,20), (47,1)), n = 12,416.
Source of the record and its checks: origin/claude/voltage-lifts-search-6lfotq, research/lifts (RESULTS.md §2.0).

## Setup
- Tools come from the voltage-lifts branch (research/lifts/haar_cell.py, research/lifts/verify_haar.sh,
  research/frontier/sizelaw/small_cands.py, research/frontier/haar_gen3.c). They are run from a scratch worktree
  of that branch (not committed here), with haar_gen3 built as `gcc -O3 -march=native -fopenmp -o haar_gen3 haar_gen3.c -lm`.
- Screening is ~0.02 s per candidate (RANDSAMPLE 200); anneals are 300 s each.
- Runs: four haar_cell.py sweeps, one core each (THREADS=1, nice), order windows
  round 1: a = 6209–6240, b = 6241–6270, c = 6271–6300, d = 6301–6360; --top 12, --secs 300, --seeds 1.

## Log
- Round 1 (haar_cell.py, 4 windows, 48 anneals of 300 s, 1 seed): no solve in 6209–6360.
  Near misses: N = 6216 meta 259 24 97 at cost 1; N = 6270 meta 209 30 26 and meta 418 15 49 and N = 6275
  meta 251 25 4 at cost 2; N = 6321 meta 301 21 23 at cost 3.
- Round 2 (haar_gen3 directly, 1200 s each, 4 cores): re-anneal of the cost-1 and cost-2 near misses with seeds 2–3.
- Round 2 result: no solve. meta 259 24 97 (N = 6216) stalls at cost 1 on seeds 2 and 3 (1200 s, ~1.7e8 evals each);
  meta 209 30 26 and meta 418 15 49 (N = 6270) stall at cost 2.
- Round 3 (started): haar_cell.py sweeps N = 6361–6420, 6421–6480, 6481–6560 (top 12, 300 s, 1 seed each), plus
  one 2400 s seed-4 re-anneal of meta 259 24 97 (N = 6216).
