# w24 NOTES (handsoff-49, card "## w24": optimizer for 5+5 bases)

Start 01:31 UTC; end 02:55 UTC. Last update 02:45 UTC.

## Result in one paragraph
Generic optimizer (lo.c, SA over all 11 free cotree voltages, gauge tree = identity): best cost 70 to 78 in 150k
moves (63 to 69 s CPU each, 3 temperature settings): it does NOT reach 0 on the benchmark (0 of 3 runs).
Symmetry-restricted optimizer (sym.c, SA over 4 orbit representatives with volt(sigma e) = phi(volt(e)), sigma = diagonal
5-cycle on the base, phi = order-5 automorphism of meta:71:7:45): reaches cost 0 on the benchmark. Success 13/40 runs at
20,000 moves (classes phi(x)=5: 4/10, 25: 3/10, 57: 3/10, 54: 3/10); a hit takes 0.3 to 6 s. Every hit was checked with
apsp 4 9: RESULT VALID n = 4,970 (a rebuild of the table graph, not a record).

## Benchmark (5+5 base, meta:71:7:45, 4,970-vertex target)
| method | runs | success | time per hit (CPU) |
|---|---|---|---|
| lo.c SA, 150k moves, T 20->0.5 | 1 | 0/1 (best 70) | not found |
| lo.c SA, 150k moves, T 5->0.2 | 1 | 0/1 (best 78) | not found |
| lo.c SA, 150k moves, T 60->2 | 1 | 0/1 (best 74) | not found |
| sym.c SA, 20k moves, phi class 5 | 10 | 4/10 | ~1 s (hits at 0.5 to 6 s) |
| sym.c SA, 20k moves, phi class 25 | 10 | 3/10 | ~1 s |
| sym.c SA, 20k moves, phi class 57 | 10 | 3/10 | ~1 s |
| sym.c SA, 20k moves, phi class 54 | 10 | 3/10 | ~1 s |
Per method the cost is about 0.2 ms per evaluation (lo.c and sym.c use the same walk-bitset evaluation).
Misses take 20k moves (about 10 s). Restart-based strategies were not tried (not enough time).

## Files
- lo.c / lo: generic voltage SA (`lo BASE GROUP.bin D sa ITERS SEED T0 T1 OUT [VOLT]`; `eval` mode checks a voltage file).
  Verified: cost 0 on w16/bases/q5.volt (convention (u,x) ~ (v, g x), table from tools/groups.py "meta 71 7 45").
- sym.c / sym: symmetric SA (`sym BASE GROUP.bin D ITERS SEED T0 T1 OUT SYMFILE`).
- sym_setup.py: builds the 284 order-5 automorphisms of N = meta:71:7:45 (4 classes by phi(x) in {5,25,54,57}) and SYM_k.txt.
- symscan.py: the same ansatz over metacyclic groups N (order 498..530 list from w16); enumerates order-5 automorphisms
  via generator images, writes scan5_498_530.tsv. Groups with no order-5 automorphism are skipped.
- Rebuild of the 4,970 lift from the symmetric method: `./sym base5.txt m497.bin 9 20000 1 5 0.5 OUT SYM_5.txt`
  (writes OUT.edges; check with `../tools/apsp OUT.edges 4 9`).

## Restart-based numbers (sym.c, 5+5 base over meta:71:7:45, 20 seeds each, short runs)
- class phi(x)=5, 5,000 moves per run: 7/20 hits (about 1.2 s per run, about 3.5 s CPU per hit).
- class phi(x)=5, 2,000 moves per run: 6/20 hits (about 0.5 s per run, about 1.7 s CPU per hit).
- class phi(x)=25, 5,000 moves per run: 11/20 hits (about 1.2 s per run).
Short restarts are better per CPU second than one 20k-move run (about 22 s per hit there).

## Scan over order 498..530 (5+5 base, symmetric ansatz)
- scan5_498_530.tsv: 113 groups with an order-5 automorphism, 4,000 moves, 1 seed, up to 2 classes per group.
  No cost 0. Best 50 on meta:5:100:2 (N of order 500, two classes); best 85 on meta:25:20:2.
  Longer runs (40,000 moves, 2 seeds per class) on meta:5:100:2: best 50, 190, 90, 110. Not zero.
- scan5_cap5.tsv: the same ansatz with up to 5 classes per group, 2,000 moves, 1 seed. No cost 0 (best 85).
Identity phi gives cost about 23,000 (volt constant on orbits is degenerate); not useful.

## Scan over order 356..380 (7+7 base, sigma = order-7 base automorphism, sym7 binary)
- scan7_356_380.tsv: 41 groups with an order-7 automorphism, 4,000 moves, 1 seed. No cost 0.
  Best 119 on meta:63:6:11 (order 378, 5,292 vertices); 20,000 moves over 5 seeds give 119 or 273 (stuck).
- Test on meta:71:5:54 (order 355, 7+7 base): symmetric SA reaches cost 0 at seed 1 (1 s); apsp VALID n = 4,970.
  Not a record. File: /home/user/degree-diameter/research/squads/handsoff-49/w24/sym7_4970.edges

## Records
None. Every cost-0 lift found has n = 4,970 (the table value), so no n > 4,970 was produced.

## Next idea (not run)
Symmetric restarts (5k moves) over all order-5 classes of every group in the 498..530 list, and a different base
automorphism (a transposition or a 3-cycle, if the orbits are free) for groups without order-5 automorphisms.
