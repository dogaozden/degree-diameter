# c4 (hubs): G-invariant (3,7) graphs on 170 vertices, groups without elements of order 5

Region: {2,3}-groups (all SmallGroups of order 18, 24, 36, plus A4 = (12,3) and C2xS4 = (48,48)), n = 170, 85 per side.

## What I ran

1. G-sets. `src/gsets.g` (dosets) enumerates every admissible G-set but is far too large for these groups
   (count with `count.g`: C2xS4 has about 1.6e7 colour-preserving side combinations, C2xA4 about 2.4e6, C3xA4 about 7.8e6;
   A4 about 4400). I wrote `gsets_few.g` (same admissibility rules, same `writegset`), which lists the multisets of
   orbit types per side with the fewest orbits first, capped per group (CAP 30-60). Driver: `run_few.sh` (`run_few_long.sh`
   for the slow GAP cases). Per group: `gs/n170/gORDER_ID/f_*.txt` (group files) and `est.txt` (PROBE estimate, orbit description).
   Colour-reversing G-sets (index-2 kernel) are included, 660 such lines in total.
2. Exhaustive search. `queue.py` runs `bin/orbdfs FILE 7` on every G-set (TL 100 s, one at a time), log `runs.tsv`.
3. Local search. `mkstart.py` (orbit-level SAT: edge orbits as variables, degree 3 at one representative per vertex orbit)
   gives a G-invariant cubic bipartite start for any group file. `ls_drive.sh` runs `symbo` (inputs/r3b_symbo.c, compiled to `symbo`)
   on the first 3 SAT-feasible colour-preserving families per group.

## Results

- orbdfs: 1502 G-sets settled, DONE with 0 solutions (groups of order 12 (A4), 18, 24, 36, 48 (C2xS4) in the capped lists).
  Most die at the root (nodes <= 5): e.g. a fixed vertex whose three neighbours have no orbit of total size 3.
- Unsettled (TIMEOUT at 100 s; the 1500 s unsharded run on f_6 also did not finish): `g12_3/f_5.txt` (PROBE 9.1e5),
  `g12_3/f_6.txt` (PROBE 9.4e3, real tree much larger), `g24_6/f_4.txt` (colour-reversing, PROBE 8.2e3).
- Not done: G-sets beyond the per-group caps (the census is far larger than the caps; see count numbers above);
  groups of order 2^a and 3^b, and any {2,3}-group of order above 48.
- Local search (symbo, 40 s each, 11 families): best score37 far 868 (g24_3 f_56). 
- Best graph of this card: `best_far132_A4f6.edges`, far 132, diam 8, connected cubic bipartite, from family A4 f_6
  (orbits 12x6,6,4,3 per side), `symbo` 60 s from a SAT start, saved from `ls/a4f6_s1_best.edges`. A further 240 s
  continuation (`ls/a4f6_cont`) reached raw proxy 126 but score37 far 135, so it was not kept.

## Problems found

- SHARD in `src/orbdfs.c` was not additive with the binary I first used (g24_3/f_53: unsharded DONE nodes=927, two
  depth-2 shards summed to 17 nodes; g12_3/f_6: 64 depth-3 shards summed to 1615 nodes). Opus reports the cause (pass-through
  calls reused a depth, so the shard filter could fire twice on one path) and a fix in bin/orbdfs. Rechecked with the fixed
  binary: shards m=2 sum to 936 and m=3 to 945 nodes on g24_3/f_53 (unsharded 927; the extra nodes are the shared upper levels).
  All settlements above are unsharded. The earlier sharded numbers are invalid and nothing rests on them.
- symbo's cost counts only same-side pairs at distance > 6 and ignores connectivity, so its proxy can differ from score37
  (the 126 vs 135 case above). On colour-reversing families symbo wrote an invalid best file (maxdeg 8, not simple,
  `g18_3/f_1`), so those were excluded.
- Many G-sets have no G-invariant cubic bipartite graph at all (mkstart UNSAT), e.g. 26 of 36 for `g18_3`.

## Files

- `runs.tsv` (orbdfs per G-set), `ls_results.tsv` (symbo per family), `gs/n170/*/est.txt`, `best_far132_A4f6.edges`
- Long unsharded orbdfs on `g12_3/f_6`: `long/a4f6.out`, 1500 s, no DONE (still unsettled). Also unsettled: `g12_3/f_5`, `g24_6/f_4`.
