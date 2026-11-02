# Card d1: faster exact solver (orbdfs_fast)

Files: squad/r2/d1/orbdfs_fast.c (source), squad/r2/d1/orbdfs_fast (binary, gcc -O2). src/orbdfs.c and bin/orbdfs untouched.

## What changed (same search tree: same options, same order, same prune decisions)
- Edge orbits cached per unordered vertex pair (members in the original enumeration order, id = min key). The validity test
  runs over the cached members only. edge_orbit was about 14% of the time before and is about 7% now.
- Collision walk rewritten level by level: level k holds the NB walks of length k as (end, previous) arrays; endpoints of the
  even levels are marked in a bitset (distinct count = bits set, updated incrementally). Early exit at each even level once
  collisions > delta. This was the main gain (about 2x on the walk).
- Fail-first: the representative that failed last is tested first. Result unchanged (AND over representatives).
- Duplicate-id tests in the A and C option lists use stamp arrays.

## Tried and dropped
- Re-testing only representatives within distance D-2 of a new edge (the idea 2 of the card): it skipped almost nothing,
  because a G-orbit of new edges has endpoints spread over the whole graph (8.5M collision walks vs 9.0M), and its BFS was
  39% of the run time. Removed.
- Iterative explicit-stack walk: slower per walk than the recursive original.
- Sentinel adjacency (fixed loops of 3): slower. Incremental distinct-count vs popcount: within noise.

## Statistics (orig, r2f_grp168, MAXSOL=1000)
- 4.29M prunes, 0.48M pass (11%); 3.52M fail at the root representative (index 0).
- Average 9.8 representatives per passing prune; 2.1 walks per prune on average. Passing prunes need all representatives,
  so the walk itself is the remaining cost (about 80-90% of the time).

## Correctness (all matched bin/orbdfs)
- inputs/r2f_grp168_f21.txt, MAXSOL=1000: nodes=619184 sols=96; SOL lines byte-identical to the original's stdout.
  src/iso.py on the 96 solution files: 2 isomorphism classes (72 + 24).
- runs/f20rev/f20rev_b1.txt: nodes=403559 sols=0 (match). f20rev_b3.txt: nodes=4695962 sols=0 (match).
- runs/val/*.txt (14 files incl. twin28_2) at D = 5, 7, 13: nodes and sols identical in every row. The 9 files run to
  completion (MAXSOL=1000000) also have identical solution-file sets (sorted md5). The z-group files ran to completion.
  twin28_2 D=5, 7, 13 hit a cap (MAXSOL 5000 or 1000): both binaries stopped after the same node counts (4655504 at D=5,
  21563 at D=13, 45721 at D=7), and the SOL streams are identical.

## Timings (CPU seconds from the solver's own clock, back to back, nice -n 15, machine loaded at about 12)
- f20rev_b3 (score): reference 35.5, 36.2; fast 22.2, 22.6. Speed-up about 1.6x.
- r2f_grp168 (MAXSOL=1000): reference 8.4, 8.8; fast 4.8 to 5.0. About 1.75x (both at -O2).
- twin28_2 (|G|=2, n=28): D=5 reference 10.2, 10.4; fast 12.5, 12.9, i.e. the fast build is about 20% SLOWER here
  (small L=4, many representatives); D=13 reference 12.8, fast 8.7.
