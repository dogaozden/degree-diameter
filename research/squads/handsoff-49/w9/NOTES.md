# w9 NOTES: bi-coset graphs of simple/perfect groups with larger stabilizers (follows w7)

Start: 2026-10-31 23:06 UTC. Deadline: about 01:05 UTC (2 hours). Last update: 00:43 UTC (final).

## Plan
- Reduction used: S = HSH is a union of left cosets Hs; only the 4 cosets L = {cid(s)} matter, and L must be a union of
  right-H orbits on the cosets. Table T[c][i] = cid(rep_c * rep_i) (M x M), so each evaluation is 2 BFS on 2M vertices.
  Exhaustive search over all such L gives the exact minimum for each (G, H) class.
- Code: grp9.py (groups, subgroup classes up to conjugacy, table export), bi9.c (exhaustive/random search over L).
- Calibration target: PSL(2,25), H order 3 must reproduce w7's exact minimum C = 30 at n = 5200.

## Tool status (23:20 UTC)
- bi9.c + grp9.py work. Calibration: PSL(2,25), H order 3 -> exact minimum 30 at n = 5200 (same as w7), apsp diameter 10.
  Edge list runs/PSL2_5^2_h3_K0.edges (apsp VALID at 10, INVALID at 9).
- Exhaustive over S is cheap: M ~ 2500-3000 cosets, 10^4..10^6 evaluations per (G,H) class, about 50 us each.
  Subgroup classes of order h are found by random normalising chains and deduplicated by conjugacy canonical form.
- Connectivity note: if every orbit of right-H action on cosets of size <= 4 lies in N(H), the graph is disconnected
  (e.g. PSL(2,31) with C_5, PSL(2,32) with C_11): these cases are skipped by the search (no valid L with diameter).

## Results (exact minima for the bi-coset family per (G,H) class; 'sampled' = partial enumeration)
Cost C = far(A0)+far(B0); far pairs = M*C/2. Every edge list below was checked with apsp (diameter 10 when C>0).

| group | H (class) | n | best C | status | file |
|---|---|---|---|---|---|
| **S7** | involution, class K2 | **5040** | **15** | EXACT (all {2,2}, {2,1,1}; {1,1,1,1} disconnected) | runs/S7_h2_K2_full.edges (apsp diam 10, far 18900 = M*C/2) |
| S7 | involution K1 | 5040 | 86 | sampled (300k of 778k) | runs/S7_h2_K1.edges |
| S7 | transposition K0 | 5040 | 140 | {2,2} exact (992); {2,1,1} sampled 2M of 8.6M (140) | runs/S7_h2_K0_full.edges |
| A7x2 | non-central involution K1 | 5040 | 50 | EXACT | runs/A7x2_h2_K1_full.edges |
| A7x2 | non-central involution K0 | 5040 | 64 | EXACT | runs/A7x2_h2_K0_full.edges |
| A7x2 | central involution (= Haar graph of A7) | 5040 | 6 | sampled (w1's Haar value) | runs/A7x2_h2_K2.edges |
| M11 | order 3 (1 class) | 5280 | 38 | EXACT | runs/M11_h3_K0.edges |
| PSL(2,25) | order 3 (1 class) | 5200 | 30 | EXACT (= w7) | runs/PSL2_5^2_h3_K0.edges |
| PGL(2,25) | order 6, class K2 (of 3) | 5200 | 30 | EXACT (K0 10368, K1 424) | runs/PGL2_5^2_h6_K2.edges |
| PSigmaL(2,25) | order 6 (7 classes) | 5200 | 382 | EXACT (best classes K2, K4) | results.tsv |
| PSL(2,27) | order 3 | 6552 | 176 | EXACT (= w7) | results.tsv |
| PSL(2,29) | V4 (1 class) | 6090 | 124 | EXACT | results.tsv |
| PSL(2,41) | A4 (2 classes) | 5740 | 530 | EXACT | results.tsv |
| A8 | order 8 (12 classes) | 5040 | 168 | EXACT for K0; others 598..10000 | results.tsv |
| PSL(3,4) | order 8 (9 classes) | 5040 | 354 | EXACT per class (best K1/K3/K4) | runs/psl34_h8.log |
| PSp(4,3) | order 9 (4 classes) | 5760 | 7942 | EXACT per class | runs/psp43_h9.log |
| PSL(2,31) | C5 | 5952 | 11880 | disconnected (only fixed cosets) | runs/psl31_h5.log |
| PSL(2,37) | C9 | 5624 | 11232 | disconnected (no size-3 orbits) | runs/psl37_h9.log |
| PSp(4,3) | order 10 | 5184 | none | no admissible orbit structure | runs/psp43_h10.log |

Two-subgroup family S = K S H (bi9b, two_sub.py), H = S7 K2:
- K conjugate to H (10 random conjugates + class rep): every one gives exact-looking 15 (cap 20000 per partition).
- K in the transposition class: 92 (sampled, cap 20000). K in the double-transposition class: 28 (sampled, cap 600k).
- So the K variation does not beat 15 for S7.

## Summary for the coordinator
- Best n >= 4972 in the bi-coset family from this card: **n = 5040, C = 15** (S7, triple-transposition involution H,
  exact). Graph: runs/S7_h2_K2_full.edges (verified apsp diam 10; 18900 far pairs). Not valid.
- Next idea: use the S7 K2 graph (18900 far pairs, about 7.5 far partners per vertex on average) as a start for w6-style
  2-switch surgery on edge pairs that are far-critical, or add/remove a handful of edges to reach cost 0 at n = 5040.
- Not worth more work in this family: PSL/PGL/PΣL(2,25), M11, A8, PSL(3,4), PSp(4,3), PSL(2,29/31/37/41) all >= 30.

## Notes on the card
- PSL(2,31) with C5, PSL(2,37) with C9 and PSL(2,32) with C11 (not run): every orbit of H on cosets has size 1 or too large,
  so L lies in N(H) and the graph is disconnected. Same for PSL(3,4) with C7 (n = 5760).
- Subgroup classes are found by random sampling (normaliser chains, 250-3000 trials). A class can be missed; the counts per
  group come from the sampler, not from a full classification.
- Tools: grp9.py (groups, subgroup classes, table export), bi9.c/bi9 (exhaustive or capped sampling over L),
  bi9b.c/bi9b + two_sub.py (two-subgroup variant). Calibrated against w7 (PSL(2,25) 30, PSL(2,27) 176).

## Rebuild commands (runs/*.bin were deleted to save disk; they are regenerated in seconds)
- S7 K2 (best, n = 5040, C = 15): `CAP=2000000 python3 grp9.py S7 2 3000` (writes runs/S7_h2_K2.bin and .edges), then
  `CAP=2000000 ./bi9 runs/S7_h2_K2.bin exh 0 out.edges`. Verified: `./apsp out.edges 4 10` VALID, `./apsp out.edges 4 9` INVALID.
- PSL(2,25) order 3 (C = 30): `python3 grp9.py PSL2_5^2 3 1500`.  PGL(2,25) order 6 class K2 (C = 30): `python3 grp9.py PGL2_5^2 6 400`.
- M11 order 3 (C = 38): `python3 grp9.py M11 3 1500`.  Generated tables: bi9 input format is in bi9.c's header comment.

## Late check (00:45 UTC)
- Two-subgroup family for PGL(2,25), H = C6 class K2 (the C = 30 class): random conjugates K = g^-1 H g give 10368 (every
  one, exhaustive: only ~70 candidates), i.e. disconnected-type; one order-6 class K with the other shape gives 10368 too.
  No gain over C = 30. (K = H itself was validated on S7 only, where it reproduced 15.)
- Final: best n >= 4972 in this family = S7 involution K2, n = 5040, C = 15 (exact). Nothing valid (no record).
