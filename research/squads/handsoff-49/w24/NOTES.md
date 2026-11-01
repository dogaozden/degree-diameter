# w24 NOTES (handsoff-49, card "## w24": optimizer for 5+5 bases)

Start 01:31 UTC; end 02:55 UTC. Last update 02:15 UTC.

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

## Scan over order 498..530 (5+5 base, symmetric ansatz, 4,000 moves per run, 1 seed)
Partial as of 02:14 UTC: no cost 0 so far; best cost 50 on a few groups. The scan is slow (python automorphism
enumeration plus runs) and runs in chunks under 110 s. See scan5_498_530.tsv.

## Next idea (not run)
Restarts with 5k-move runs (expected time per hit may be lower), and the symmetric ansatz for the 7+7 base over orders
356..380 (base automorphism of order 7 and order-7 automorphisms of N).
