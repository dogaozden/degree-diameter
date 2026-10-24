# exp2-alone-6: report

Worker: one Haiku session, working alone (no subagents). Target: cells (7,7), (9,7), (11,7) of the bipartite (Δ, D) table.
Start 2026-10-24 16:56 UTC; last search stopped about 17:17 UTC.

## Result

No cell is beaten. Best valid sizes (each checked with `research/frontier/build_haar2.py`: VALID, two BFS from (e,A) and (e,B), diameter 7, all vertices reached):

| cell | table (vertices) | best valid (vertices) | ratio | group | how found | file |
|---|---|---|---|---|---|---|
| (7,7) | 23,436 | **18,720** | 0.799 | SL(2,9) × Z13 (N = 9,360) | random S, 1.2 s | research/frontier/sols/d7D7_sl9x13_rand_s1.txt |
| (9,7) | 117,648 | **82,992** | 0.705 | SL(2,13) × Z19 (N = 41,496) | orbit k=3, f=0, 2 s | research/frontier/sols/d9D7_sl13x19_orb3f0_s1.txt |
| (11,7) | 398,580 | **266,448** | 0.669 | SL(2,13) × Z61 (N = 133,224) | orbit k=3, f=2, 13 s | research/frontier/sols/d11D7_sl13x61_orb3f2_s1.txt |

Vertices = 2N for a Haar graph. The score ratio is best valid size / table value. (For reference, an earlier (7,7) graph on SL(2,11) × Z7, 18,480 vertices, is also saved in research/frontier/sols/d7D7_sl11x7_rand_s1.txt.)

## Why no cell can be beaten with this method (computed before searching)

Using the counting convention in research/frontier/SIZE_LAW.md (W = binding words, μ = N·e^(−W/N), the expected number of uncovered elements for a random S):

- **(7,7)**: to beat 23,436 we need N ≥ 11,719. There W = 55,987 and μ ≈ 99. The first-moment ceiling is about N_h = 10,928 (the table is 7% above it).
- **(9,7)**: need N ≥ 58,824. W = 299,593 and μ ≈ 361. Ceiling N_h = 48,252 (table 22% above).
- **(11,7)**: need N ≥ 199,290. W = 1,111,111 and μ ≈ 755. Ceiling N_h = 156,861 (table 27% above).

The ceiling formula was calibrated on even D. I used the same convention for odd D, which is how STRUCTURE.md reports μ for odd cells. So these are estimates, not proofs. The measured walls agree with them:

- Orbit search (haar_sym, k = 3) solved (9,7) at μ ≈ 30 and (11,7) at μ ≈ 32 in seconds. At μ ≈ 38 it stalled at 6–12 uncovered after 900 s (about 3–28 million evaluations).
- Random S at (9,7), SL(2,13) × Z19 (μ ≈ 30): stalled at 10 uncovered after 5.6 million evaluations. The orbit version solved it in 70,000 evaluations.
- (7,7): random S solved μ ≈ 22 quickly. At μ ≈ 24 (SL(2,9) × Z13) it solved in 50,000 evaluations. At μ ≈ 48 (SL(2,7) × Z31) orbit mode stalled at 6 uncovered in three seeds, each about 8 × 10⁷ evaluations.

So the reachable N is about 0.8–0.9 of N_h for these cells, and that is 10–25% below what the table needs. Going from μ ≈ 38 to μ ≈ 99 needs far more compute than the 4-hour budget allows (the evaluation count grows roughly like e^(μ/4.5)).

## What I tried

1. Compiled `haar_sym.c` from branch `claude/structured-search-orbit-w5dd4f` (research/structured/). Kept the binary and source out of this branch (`research/squads/exp2/.gitignore` excludes `src/`).
2. Random-S control at (9,7), SL(2,13) × Z19: stalled at 10. Orbit mode on the same group solved. This is the clearest evidence that the orbit method is the right lever.
3. Ladder for (9,7) (`research/squads/exp2/ladder.sh`, orbit "3 3 0"):
   - SL(2,13) × Z19, 41,496: solved (kept).
   - SL(2,7) × Z127, 42,672 (μ ≈ 38): stalled at 12. Not solved.
   - SL(2,9) × Z61, 43,920 (μ ≈ 48, characteristic 3): stalled at 10. Not solved.
4. Ladder for (11,7) (orbit "3 3 2"):
   - SL(2,13) × Z61, 133,224: solved in 13 s (kept).
   - SL(2,11) × Z103, 135,960 (μ ≈ 38): stalled at 6 after 900 s.
   - SL(2,7) × Z409, 137,424: stalled at 78 (a bad group for this orbit).
5. (7,7), in order of size:
   - SL(2,11) × Z7, 9,240, random: solved in 0.1 s.
   - SL(2,9) × Z13, 9,360, random: solved in 1.2 s (kept, best).
   - SL(2,5) × Z79, 9,480, random: stalled at 16.
   - SL(2,8) × Z19, 9,576, random: stalled at 4 after 5.5 × 10⁷ evaluations (characteristic 2, many involutions, bad for odd D).
   - SL(2,7) × Z31, 10,416, orbit "3 2 1" (μ ≈ 48): stalled at 6 in three seeds. Random S on the same group reached only 22.

## What worked

- **Orbit mode (k = 3) beats random S** on the larger cells. The same group that stalls at random S is solved in seconds by the orbit search.
- **SL(2,q) with q odd or small** (not PSL) is the right family for odd D. PSL has many involutions, which is bad for odd D.
- Choosing the group by its μ (the expected number of uncovered elements) predicted the solves: μ ≲ 30 solved quickly, μ ≈ 38 needed far more time, and μ ≳ 40 stalled in every run.

## Checks

Every reported file was checked by `research/frontier/build_haar2.py` (independent of the C code). Runs were single-threaded, up to four at a time.

## Budget and time

- `research/squads/usage/exp2-alone-6.jsonl` logs the session usage. Final check at 17:17 UTC: budget_units = 0.0071 (the cap is 1.5).
- Wall time: about 21 minutes (16:56 to 17:17 UTC). I stopped there because the remaining candidates had all stalled and the gains left (about +0.02 to +0.05 in ratio) were small.

## Not done

- No k = 5 orbits, no 2+2 lifts, no voltage lifts (research/lifts/), no Lean work.
- No search on groups other than SL/PSL/PGL-type with Z_n factors.
- If someone wants to push (9,7) and (11,7) further, the next step is more time on SL(2,7) × Z127 and SL(2,11) × Z103 at μ ≈ 38 (more seeds, longer runs). Expect a few percent at most.
