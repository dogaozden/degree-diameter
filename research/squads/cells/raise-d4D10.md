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
