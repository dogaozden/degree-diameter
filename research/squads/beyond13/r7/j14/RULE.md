# j14: where does metacyclic random S beat SL/PSL orbit S?

All values are vertex counts 2N of Haar graphs (N = |G|). "Verified" = a haarcheck_gen or metacheck VALID file exists
(runs/*.gen.txt in research/frontier/beyond13/ or a metacheck line in the squad card). Sources: cells.txt, cells_other.txt,
BEYOND_TABLE.md rows for D = 11, 12, squad scoreboards r1-r6.

## 1. Every comparison (meta random S vs SL/PSL orbit S, same D)

| Δ | D | best metacyclic random S (group, k, 2N) | best SL/PSL orbit S (group, 2N) | ratio R = meta/orbit | status |
|---|---|---|---|---|---|
| 4 | 11 | Z1093 x|901 Z13, k=13: 28,418 (i05); Z599 x|498 Z23: 27,554 (f15) | PSL(2,29), orbit: 24,360 | 1.167 | both verified |
| 4 | 12 | Z1277 x|964 Z29, k=29: 74,066 (h08) | SL(2,17) x Z7, orbit: 68,544 | 1.081 | verified |
| 4 | 13 | Z2237 x|1984 Z43, k=43: 192,382 (h03); Z4903 x|230 Z19: 186,314 (c15) | PSL(2,29) x Z7, orbit scan {e,x,ax,a²x}: 170,520 (c05) | 1.128 | verified |
| 4 | 14 | Z2731 x|2400 Z91, k=91: 497,042 (i04); Z4027 x|2950 Z61: 491,294 (h04); Z7001 x|4532 Z35: 490,070 (g13) | PSL(2,41) x Z7, "3 1 1": 482,160 (c06) | 1.031 | verified |
| 4 | 9 | Z101 x|5 Z25: cost 2 at 5,050 (i09) | 2013 record 4,970 (no job orbit value) | none valid; near miss | |
| 4 | 10 | Z109 x|12 Z54: cost 2 at 11,772 (director) | 2013 record 11,748 | none valid; near miss | |
| 5 | 10 | Z1567 x|871 Z29: 90,886 (i10, apsp) | 2013 record 90,068 (no job orbit value) | 1.009 vs 2013 | verified, not orbit |
| 5 | 11 | Z5279 x|1922 Z29: 306,182 (h07) | SL(2,53), orbit: 297,648 (beyond11) | 1.029 | verified |
| 5 | 12 | Z9859 x|4192 Z53, k=53: 1,045,054 (i08); Z17981 x|15904 Z29: 1,042,898 (h08) | PSL(2,53) x Z7, orbit: 1,041,768 (beyond11) | 1.003 | verified |
| 5 | 13 | Z72497 x|9840 Z23, k=23: 3,334,862 (e02, metacheck). Products of two Frobenius groups: 3,594,910 (i06), 3,577,750 (h05) | PSL(2,47) x Z31, "3 1 2": 3,217,056 (c07) | 1.037 single; 1.117 product | verified |
| 5 | 14 | none tried in a metacyclic group. Non-metacyclic SL(2,97) x Z7 random S: 12,776,064 (h06) | none valid: "3 1 2" stalls at cost 18 (c08) | n/a | |
| 6 | 11 | Z17203 x|9845 Z61, k=61: 2,098,766 (i11) | SL(2,29) x Z43, orbit: 2,094,960 (beyond11) | 1.002 | verified |
| 6 | 13 | Z331231 x|58155 Z61: cost 2 at N = 20.2M, i.e. 2N = 40,410,182 (e03); best cost 4 at N > 20.9M (i13) | PSL(2,83) x Z73, "3 2 0": 41,734,392 (f11) | meta fails: near miss 0.968 | orbit verified |
| 6 | 14 | none tried in metacyclic | SL(2,97) x Z103, "3 2 0": 187,990,656 (g07) | n/a | verified |
| 3 | 11-14 | exhaustive {e,x,y} metacyclic (1,474 / 2,394 / 2,176) and non-metacyclic A6 x Z4 (2,880): no random-S meta value | none in job | n/a | lifts win at Δ=3 |
| 7 | 11 / 12 / 13 / 14 | none tried | SL(2,53) x Z37: 11,012,976; PSL(2,67) x Z199: 59,838,504; SL(2,229) x Z13: 312,227,760 (e10); SL(2,163) x Z193: 1,671,605,424 (f13) | n/a | verified except the last two only at D = 14 (f13 verified; g06, h14 not) |
| 8 | 13 / 14 | none tried | SL(2,499) x Z7: 1,739,514,000 (verified); PSL(2,397) x Z181 at D = 14: no check file | n/a | |
| 9 | 13 | none tried | SL(2,661) x Z13: 7,508,907,120 (verified); SL(2,593) x Z19 (s6): 7,924,036,032 but no check file yet | n/a | candidate, unchecked |
| 10 | 13 | none tried | PSL(2,503) x Z157: 19,980,294,768 (verified, cap) | n/a | |

Summary of R (verified rows): Δ=4: 1.167 (D11), 1.081 (D12), 1.128 (D13), 1.031 (D14). Δ=5: 1.029 (D11), 1.003 (D12),
1.037 (D13), 1.009 (D10, vs 2013). Δ=6: 1.002 (D11), 0.968 (D13, meta cost 2). Δ = 7..10 and Δ = 5, D = 14: no metacyclic data.

## 2. The rule (fit to the table above)

Mean ln R per Δ (verified rows):

| Δ | odd D | even D | all |
|---|---|---|---|
| 4 | +0.137 (1.167, 1.128) | +0.055 (1.081, 1.031) | +0.096 |
| 5 | +0.033 (1.029, 1.037) | +0.006 (1.003; D10 1.009 not orbit) | +0.019 |
| 6 | -0.015 (1.002, 0.968) | none | -0.015 |

**Rule.** Random S on an odd-order metacyclic group of large k (k >= 13) beats the best SL/PSL orbit S by a few percent,
and only while the orbit form is rigid: Δ = 4 (one free element) gains 3-17 %, Δ = 5 (one fixed generator plus one orbit,
two free elements) gains 0-4 %, and Δ = 6 is break-even (1.002 at D = 11, cost 2 at D = 13). Δ >= 7 has no metacyclic
evidence yet. The gain is roughly twice as large at odd D as at even D for the same Δ (log-ratio 0.137 vs 0.055 at Δ=4,
0.033 vs 0.006 at Δ=5). Within the tested range, k >= 13 is the only k condition: k = 1, 3, 5 are near-abelian (word cover
1 %, 6 %, 73 %; r2/e11), and every k from 13 to 91 has produced a record. Nothing in the data prefers one k.

**Why, even D (Δ = 4).** The orbit form {e, x, ax, a²x} has one free element x: about N/3 candidates, versus about N³/6
random S (i12 CANDIDATES.md: ln C = 15 vs 47 at N = 1e7). The orbit search (orbscan) is exhaustive over x and stops at
170,520 (D = 13); the random-S family still has candidates at much larger N. This is a freedom gap, so it appears at
even D too, with a smaller margin (no involution/central floor to remove, so only the count matters). The statement in
THEORY.md section 1 that "at even D metacyclic groups gave no gain (r2/e06)" is superseded: r5/h08 (4,12, +8 %) and
r6/i04 (4,14, +3 %) show gains at even D with large k. r2/e06 used k = 19-35 and cost 1-2; the large-k runs succeeded.

**Why, odd D.** Odd-order groups have no involutions and (for Frobenius groups) trivial centre, so the ODD_D_HOLES floors
disappear (THEORY.md section 1). SL/PSL(2,p) x Z_n at odd D carry a central or involution floor (i12: SL(2,37) x Z397 has
median cost about 250 for random S and a best-orbit floor near 200; r1/c14 measured -I missing 20-46 % of random S in SL).
That floor is what the metacyclic groups avoid, hence the larger odd-D margin (Δ = 4: 1.13-1.17 vs 1.03-1.08).

**Why it stops at Δ >= 6.** Counting alone predicts the opposite trend (random S has 5 free elements against 2 for the
orbit forms at Δ = 6, so random S should win more). The data does not follow the count. i12 measured that random S on
metacyclic groups has a much heavier lower tail than the size law mu predicts, and the orbit form on a metacyclic group
is broken outright (median 80 % of G uncovered; alpha acts as scaling, so orbit elements may generate a proper subgroup;
unchecked). At Δ = 6, odd D, the metacyclic random-S search stops at cost 2 (2N = 40.4M) while the PSL orbit reached 41.7M.
So the crossover is near Δ = 6, and the mechanism at Δ >= 6 is the hole tail, not the count. This is a hypothesis to test.

## 3. Corrections found while collecting (for the director)

- cells.txt / SECTION_D13.md: the (8,13) record is SL(2,499) x Z7 at 2N = 1,739,514,000 (its gen check is VALID; the
  stale "1,676,500,800" line was the earlier SL(2,401) x Z13 value). Table row needs the update.
- (7,14): f13 (SL(2,163) x Z193, 1,671,605,424) is verified; g06 (1,673,976,240) and h14 (PSL(2,223) x Z151, 1,674,490,944)
  have cost-0 claims but no check file.
- (9,13): SL(2,593) x Z19 (s6) would be 2N = 7,924,036,032 > 7,508,907,120 but has no check file and no RESULT line.
- (4,9), (4,10): the meta near misses (5,050 at cost 2; 11,772 at cost 2) are above the 2013 values 4,970 and 11,748. Not
  valid; a k = 25 / k = 54 run at more evaluations is the obvious next step.

## 4. Next

Test the Δ = 6 crossover directly: at D = 11 and D = 13, run hmeta random S on metacyclic groups with k >= 13 at N near 1e7 (2N near 2e7), and measure the lower tail (RANDORB, 300 samples, hit rate) for both random meta and PSL orbit S at Δ = 6,
to see whether the meta hit rate falls below the PSL orbit's before N does. Check <S S^-1> = G before any orbit run on a
metacyclic group (i12 hypothesis).
