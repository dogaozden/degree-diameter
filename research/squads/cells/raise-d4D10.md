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
- Round 3 result: no solve in 6361–6560. Each window 12 anneals of 300 s. Near misses: N = 6394 meta 278 23 45 and
  meta 139 46 6 at cost 1; N = 6510 meta 217 30 38 at cost 3. The 2400 s seed-4 re-anneal of N = 6216 ended at cost 1.
- Round 4 (started): the four round-1 windows, resumed to top 30 (18 new candidates each, 300 s, seed 1).
- Round 3 finished: sweeps N = 6361–6420, 6421–6480, 6481–6560 gave no solve (12 anneals each).
- Round 4 finished: the four round-1 windows resumed to top 30 (18 new anneals each, 300 s). No solve.
- Non-Haar check: lift.c, K_{4,4} base (8 vertices), cyclic groups Z_1500, Z_1520, Z_1552, Z_1553 (n = 12,000 to
  12,424). Final costs after 63 s: 974, 1,100, 1,190, 1,292 for Z_1500, Z_1520, Z_1552, Z_1553 (start 3,326–7,832). That is far from cost 0, so this route was dropped
  before any long run finished. The earlier voltage-lift sweeps only reached n ≈ 11,750 on these bases.

## Totals and status (Haar, N = 6209–6560)
- About 150 anneals of 300 s (rounds 1, 3, 4) plus 4 re-anneals of 1200–2400 s (round 2 and the seed-4 run).
- Best costs: N = 6216 meta 259 24 97 at cost 1 (stalled over seeds 1–4, up to 2400 s); N = 6394 meta 278 23 45 and
  meta 139 46 6 at cost 1 (300 s, one seed each, not re-annealed yet); N = 6270 at cost 2.
- No new Haar solution above N = 6208. No file saved to research/frontier/sols/ (nothing verified).

## Stop decision
Stopped after about 3.5 h of the 6 h budget. Reasons:
- The record's own order (6208) came from about the 10th anneal of a broad pass. Haar sweeps above it have now run
  about 150 anneals over N = 6209–6560 without a solve, and the closest candidates stall at cost 1 even on long runs.
- The non-Haar K_{4,4} lift is far off (cost ~1000 after 30 s).
- Untried, for the coordinator: (a) re-anneal the cost-1 candidates at N = 6394 for 1200 s with 2 seeds; (b) non-metabelian
  groups (sl/psl/pgl × Z_n) at N = 6209–6330, annealed with more seeds, since the (5,7) and (5,8) lessons say the
  metacyclic score understates them; (c) lift.c with a 2+2 or dipole-plus-matching base at n > 12,416 (none was run there).

## Files
- research/squads/cells/raise-d4D10.md (this file). The search scripts are in origin/claude/voltage-lifts-search-6lfotq,
  research/lifts; they were run from a scratch worktree and are not committed here.
