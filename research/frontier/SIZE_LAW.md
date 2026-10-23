# The Haar size law: |G| ≈ C_D (Δ−1)^(D−2), explained, tested and used

frontier size-law agent (Opus), 2026-10-23, Mac mini. Starting point: Kenaznia's note
`~/kenan/notes/haar-size-law-2026-10-22.md`. Fit data: `size_law_fits.csv` (this folder).

## 0. Short answer

1. **The regularity is real, but C_D is not a constant.** Over every solution file, N := |G| fits
   N = C_D (Δ−1)^(D−2) within each D to 2–6 % (slope of log N against log(Δ−1) is D−2 within error at D = 5, 8, 9, 10,
   not D−1). But C_D is the slowly varying quantity Δ·g/ln(N/μ\*), not a constant: it grows with Δ and falls like 1/D.
2. **Explanation (coupon collector).** The diameter condition says that W ≈ Δ(Δ−1)^(D−2) words of length ≤ D−1 must
   hit all N group elements. If the words behave like independent random elements, the expected number missed is
   μ = N e^(−W/N). A search succeeds when μ ≤ μ\*, a small number set by how hard we search (μ\* ≈ 9–40). Solving
   W/N = ln(N/μ\*) gives N ≈ Δ(Δ−1)^(D−2)/ln(N/μ\*), i.e. Kenaznia's law with C_D = Δg/ln(N/μ\*). C_D ≈ 1 at D = 8 is
   a numerical coincidence (ln(N/μ\*) happens to be ≈ Δ there). The "decay ~0.8 per step of D" is
   ln(N_D/μ\*)/ln(N_{D+1}/μ\*) ≈ 1 − ln(Δ−1)/ln(N/μ\*): 0.79 then 0.84 at Δ = 8, heading to 0 like 1/D. It is not a
   geometric sequence.
3. **One law fits every record with two parameters:** ln μ\* = 4.34 − 0.123 ln N (fitted on the best Haar graph in each of the 19 cells with data, all D).
   Leave-one-out prediction error 2.2 % rms in N (all cells except the small D = 5, Δ = 5 one).
4. **Tested out of sample today in seven untried cells**, by running haar_gen3 at the predicted order. Every one beat
   the table, and the law said in advance which runs would solve: (10,10) **+15.0 %**, (12,9) **+9.2 %**, (13,9)
   **+21.9 %**, (14,9) **+17.2 %**, (15,8) **+16.3 %**, (15,9) **+13.6 %**, (16,9) **+9.6 %** (vertex counts in §3.2).
   In every run, it solved iff μ ≤ μ\*(N). These are new cells for us. All seven pass an independent low-memory C
   checker written this session, and build_haar2.py also passes (15,8), (12,9), (10,10) and (13,9). None are harvested; the
   solution files are copied in Appendix A.
5. **Walls are the μ\* curve.** At (7,8), μ = 13 solves in seconds, μ ≈ 20 solves in a few of 8 runs per 90 s, μ ≈ 30
   never solves. The number of evaluations needed grows like e^(μ/2), so 10× more compute buys only about 3–4 % in N. The
   counting ceiling N_h of heuristic.py corresponds to μ = Δ ln N ≈ 70–200, far out of reach of search. Walls are
   fundamental for annealing over random-like S. Symmetric S (orbits of an automorphism) was tested and is worse
   (§4.2).
6. **Theorem direction.** A family with |V| ≥ c(Δ−1)^(D−2) for *constant* c and all large D is **not** what random-like
   Haar graphs give. They give c_D ~ Δ/(D ln(Δ−1)) → 0. The honest target is |V| ≳ 2Δ(Δ−1)^(D−2)/ln|V|. Haar graphs beat
   random regular graphs here by a factor of about 2 in the logarithm, because vertex-transitivity means only one
   vertex has to be covered, not all pairs. A rigorous version needs equidistribution of pairs of words of length
   ~log N in SL(2,q) with random generators. That is beyond current technology (§5).

## 1. Is the law real?

Data: all 82 haar_gen/haar_gen3 solution files in `sols/` (D = 8, 9, 10; pulled 2026-10-23 including the
harvest at 2b50d7f0c), the 18 D = 5 files in `../d5/sols/`, and two D = 5 Haar graphs documented only in
`../d5/REPORT.md` (orders 176 and 570). N = |G|, graph order 2N. Table values: heuristic.py's TABLE (= TABLE.md).

### 1.1 Constants per D (geometric mean, sd and standard error of the mean in log space)

| D | files | C = N/(Δ−1)^(D−2), all files | best per cell: C | N/N_h (best) | μ = N e^(−W/N) (best) | 2N/Moore (best) |
|---|---|---|---|---|---|---|
| 5 | 20 | 2.54 (sd 2.9 %, se 0.6 %) | 2.65 (sd 3.0 %, 4 cells) | 0.94 | 35 | 0.36 |
| 8 | 30 | 0.94 (sd 6.0 %, se 1.1 %) | 0.98 (sd 5.1 %, 5 cells) | 0.85 | 20 | 0.12 |
| 9 | 32 | 0.75 (sd 4.2 %, se 0.7 %) | 0.78 (sd 3.3 %, 6 cells) | 0.82 | 13 | 0.09 |
| 10 | 20 | 0.62 (sd 3.2 %, se 0.7 %) | 0.65 (sd 1.7 %, 4 cells) | 0.84 | 13 | 0.085 |

So Kenaznia's numbers hold up (1, 0.77, 0.64), and D = 5 continues the sequence at 2.6.

### 1.2 Exponent

Slope of log N against log(Δ−1) per D (best per cell, bootstrap standard error):
D = 5: 2.91 ± 0.05 · D = 8: 6.11 ± 0.10 · D = 9: 7.08 ± 0.07 · D = 10: 8.03 ± 0.08. The exponent is D−2, not D−1
(that would need slopes 4, 7, 8, 9: rejected by > 10 σ). A slope slightly above D−2 is predicted (§2.2: C_D grows like
Δ/ln N); N_h itself has slopes 3.07, 6.22, 7.18, 8.12.

### 1.3 Competing laws (best per cell, rms of log residuals)

| law | free parameters | rms log-residual | max |
|---|---|---|---|
| N = C_D (Δ−1)^(D−2), one C per D | 4 | 0.032 | 0.089 |
| N = μ\*-law, ln μ\* = a + b ln N (§2.2) | 2 | 0.022 (leave-one-out, excl. (5,5)); 0.054 incl. | 0.057 / 0.22 |
| N = κ N_h, one κ | 1 | 0.057 | 0.150 |
| N e^(−W/N) = μ\*, one μ\* | 1 | 0.079 | 0.196 |
| N = c W/ln N | 1 | 0.25 | 0.62 |
| 2N = c · Moore bound | 1 | 0.58 | 1.40 |
| N = c (Δ−1)^(D−1) | 1 | 0.61 | 1.52 |

"Log-diameter" fits (diam = log_{Δ−1} N + const) are the same as one constant C, which fails across D (C goes 2.6 →
0.65). A constant fraction of the Moore bound fails worst of all.

### 1.4 What N_h is and how C_D relates to it

heuristic.py's N_h solves N e^(−W/N) = Δ ln N. That is the first-moment threshold: there are about N^Δ generator sets,
each covers everything with probability ≈ e^(−μ), so some S should exist while μ ≲ Δ ln N. Records sit at N/N_h = 0.80–0.86
for D = 8–10 (0.89–0.99 at D = 5, where N is tiny and searches are nearly exhaustive). In μ units, the records have
μ ≈ 9–25 against the ceiling's Δ ln N ≈ 70–220. The relation is C_D = κ·C_h with
C_h = Δg/ln(N_h/(Δ ln N_h)) and κ = N/N_h ≈ 1 − ln(Δ ln N/μ\*)/ln(N/μ\*). The walls at "0.79–0.86 N_h" are the same
thing as μ\* ≈ 10–25.

## 2. Why: the counting model

### 2.1 What the covering condition counts

H(G,S): (g,A) ~ (sg,B), |S| = Δ. A non-backtracking walk of length ℓ from (e,A) ends at the alternating product
s_ℓ^(±1) ⋯ s_2^(−1) s_1, and there are Δ(Δ−1)^(ℓ−1) of them. Right multiplication is transitive on each side, so:
- D = 2k (even): all of G must be reached on side B by odd lengths ≤ D−1: W = Δ Σ_{i<k} (Δ−1)^(2i).
- D = 2k+1 (odd): all of G on side A by even lengths ≤ D−1 from (e,A), and the same from (e,B):
  W = 1 + Σ_{i≤k} Δ(Δ−1)^(2i−1) per condition.
In both cases W = Δ(Δ−1)^(D−2)·g_Δ(1 + o(1)) with g_Δ = (Δ−1)²/((Δ−1)²−1) ≈ 1. That is the origin of the exponent D−2:
the binding words have length D−1.

### 2.2 Poisson model gives the law

Treat the W endpoints as independent uniform elements. Then #uncovered ≈ Poisson(μ) with μ = N e^(−W/N). A search with a
given effort reaches cost 0 when μ ≤ μ\*. Setting W/N = ln(N/μ\*) gives

  **N = Δ g_Δ (Δ−1)^(D−2) / ln(N/μ\*),  i.e.  C_D(Δ) = Δ g_Δ / [(D−2) ln(Δ−1) + ln C_D − ln μ\*].**

Fitted on the best Haar graph of each of the 19 cells with data: **ln μ\* = 4.34 − 0.123 ln N** (se 0.17 and 0.014; residual sd 0.20 in ln μ, which is
≈ 2 % in N). μ\* falls with N because evaluations get more expensive (cost ∝ N), so a fixed wall-clock budget buys fewer
of them (§4.1).

Consequences, all visible in the data:
- **Δ-dependence at fixed D.** C_D rises slowly with Δ. D = 9: C = 0.744 (Δ7), 0.756 (Δ8), 0.784 (Δ9), 0.818 (Δ11), and
  in today's new cells 0.841 (Δ12), 0.867 (Δ13), 0.905 (Δ15), 0.927 (Δ16). The model gives 0.762, 0.766, 0.779, 0.820,
  0.845, 0.870, 0.924, 0.951. Over Δ = 6..11 the rise is small, which is why C_D looked constant.
- **D-decay.** C_{D+1}/C_D = ln(N_D/μ\*)/ln(N_{D+1}/μ\*). At Δ = 8: 8.51/10.80 = 0.79 (D 8→9) and 10.80/12.81 = 0.84
  (9→10). Observed 0.79 and 0.84. Asymptotically C_D ≈ Δ/((D−2) ln(Δ−1)) → 0.
- **Diameter form.** diam H(G,S) ≈ 2 + log_{Δ−1}( N ln(N/μ\*) / (Δ g) ). That is log_{Δ−1}N + log_{Δ−1}ln N + O(1),
  the same shape as the diameter of random Δ-regular graphs (Bollobás and Fernandez de la Vega 1982).

### 2.3 Checks of the model's ingredients (measured this session)

1. **Ball growth = random model, except at the very end.** Random S over SL(2,47)×Z_6 at (8,9) (N = 622,656). Cumulative
   distinct elements after each length: 8, 57, 400, 2797 (tree: 2801), 19313, 123115, 488707, 622637. The model
   N(1 − e^(−W_ℓ/N)) gives 123,180 and 489,600 at lengths 6 and 7 (observed 120.6–123.1 k and 481.4–488.7 k over three S).
   Short-cycle losses are under 0.2 % at length 4. So "collision rates" are exactly random-like at every intermediate level.
2. **Final level: excess factor ε = (mean uncovered for random S)/μ.** It is 1.3–2.2 for the good families: SL(2,49) at
   (8,8) 1.3–1.5; PSL(2,29)×Z_9 1.6–2.2; PSL(2,19)×Z_13 at (7,8) 1.7; SL(2,47)×Z_6 at (8,9) 1.8; PSL(2,23)×Z_41 at (9,8)
   2.0; SL(2,81)×Z_2 at (7,10) 1.9. It is large for small-Q × big-cyclic groups: SL(2,8)×Z_211 ≈ 8. The distributions are
   heavy-tailed (variance ≫ mean), e.g. mean 37.6, variance 1800. ε ≈ 2 costs about ln 2/(W/N) ≈ 6 % of W. That loss is
   inside μ\* and is the reason RANDSAMPLE screening works.
3. **Not from cyclic-fiber imbalance.** For G = Q × Z_n, the number of binding words landing in each fiber Q×{z} is
   computable exactly (DP over words). The Jensen excess Σ_z |Q| e^(−W_z/|Q|)/μ is 1.000–1.005 for 68 of the 69
   solution files with n > 1 and for random z (max 1.22 for one non-record (9,8) file). The Z_n part mixes completely
   within D−1 steps, so it is not where ε comes from. The remaining excess is in the matrix part: small-order elements
   and short relations, as in HAAR_GEN_NOTES §3.
4. **D odd: uncovered elements come in inverse pairs.** The A-side word set (S^(−1)S)^k is inverse-closed. In a D = 9
   run (SL(2,23)×Z_6, 58 uncovered), 58/58 uncovered elements had their inverse uncovered too. So a D-odd condition is
   N/2 independent pair-targets hit by W/2 pair-draws. The Poisson mean in pair units is again N e^(−W/N), and the two
   conditions together give the same μ as one D-even condition.
5. **No even/odd effect beyond W.** Residuals of ln μ\* by parity: even +0.070 ± 0.046, odd −0.063 ± 0.068. The
   difference of 0.13 ± 0.08 is about 1 % in N and 1.6 σ. If D-odd words were *not* paired, odd D would sit at −0.69
   (ln 2) instead, about 7 σ away. So the even/odd question has a structural answer (inverse pairs), and it shows the two
   parities behave the same. There is no parity constant to find.

### 2.4 Relation to expanders and random graphs

Bourgain–Gamburd gives a spectral gap for random S in SL(2,p). That implies diameter O(log N) with an unspecified
constant, which is far weaker than the 1·log_{Δ−1}N + log log N we observe. Even Ramanujan graphs only give diameter ≤
2 log_{Δ−1} N. Lubetzky–Peres show typical distance log_{Δ−1}N + O(log log N) on Ramanujan graphs, and Sardari showed
LPS Ramanujan graphs have diameter ≥ (4/3) log. (These are from memory; check before citing.) So the observed law is the
**random-graph (coupon collector) law**, not an expander law. Highly structured "best expanders" are worse for this
problem than random-like S.

**Haar versus random bipartite graphs: a factor of 2 in the log.** A random bipartite Δ-regular graph must connect *every
pair* within D. That is ~N² targets, so it needs W/N ≥ 2 ln N and N ≈ W/(2 ln N). A Haar graph is transitive on each
side, so it needs only N targets: W/N ≥ ln N, N ≈ W/ln N. That is roughly why Haar graphs beat generic random
constructions by a factor of about 2 (heuristic; the "one ball" version, ln(N/μ\*), is the one the data follow).

## 3. Predictions

### 3.1 How the prediction is made

For each cell solve N e^(−W/N) = μ\*(N) with ln μ\* = 4.335 − 0.123 ln N. The ±2σ band uses the residual sd 0.196 in
ln μ\* (≈ ±3 % in N). The model is invalid where the prediction is at or above the first-moment ceiling N_h: small Δ and
small N, where the search covers a large share of all S. Those cells are flagged. D = 7 has no Haar data, so D = 7 is
interpolated. The prediction means "what our current machinery (SL(2,q)×Z_n and products, haar_gen3, minutes to hours
per order) should reach". Doubling the compute moves it by about 1 %.

### 3.2 Out-of-sample test: the untried cells (run this session, this Mac, 1 core each)

| cell | table | group | N | N/N_h | μ | μ\*(N) | result | vertices | vs table | predicted |
|---|---|---|---|---|---|---|---|---|---|---|
| (10,10) | 50,331,156 | SL(2,233)×Z_2 | 25,298,208 | 0.710 | 0.8 | 9.4 | solved, 9 evals | 50,596,416 | +0.5 % | |
| | | SL(2,241)×Z_2 | 27,994,560 | 0.786 | 4.8 | 9.3 | solved, 9 evals | 55,989,120 | +11.2 % | |
| | | **SL(2,307)** | 28,934,136 | 0.812 | 8.3 | 9.2 | solved, 10,441 evals, 642 s | **57,868,272** | **+15.0 %** | +15.7 % [+13.0, +18.6] |
| (12,9) | 30,001,152 | SL(2,197)×Z_2 | 15,290,352 | 0.747 | 3.1 | 10.0 | solved, 9 evals | 30,580,704 | +1.9 % | |
| | | **SL(2,127)×Z_8** | 16,386,048 | 0.801 | 9.2 | 9.9 | solved, 17,361 evals, 551 s | **32,772,096** | **+9.2 %** | +9.7 % [+7.0, +12.6] |
| (13,9) | 50,990,610 | SL(2,137)×Z_10 | 25,712,160 | 0.661 | 0.3 | 9.4 | random S already valid | 51,424,320 | +0.9 % | |
| | | **SL(2,109)×Z_24** | 31,078,080 | 0.798 | 8.7 | 9.1 | solved, 12,033 evals, 843 s | **62,156,160** | **+21.9 %** | +22.3 % [+19.4, +25.3] |
| (14,9) | 95,087,738 | **SL(2,191)×Z_8** | 55,741,440 | 0.791 | 7.3 | 8.5 | solved, 2,417 evals, 567 s | **111,482,880** | **+17.2 %** | +18.3 % [+15.6, +21.2] |
| (15,8) | 14,172,480 | SL(2,193) | 7,188,864 | 0.677 | 1.0 | 10.9 | solved, 9 evals | 14,377,728 | +1.4 % | |
| | | **SL(2,101)×Z_8** | 8,241,600 | 0.776 | 8.6 | 10.8 | solved, 3,345 evals, 35 s | **16,483,200** | **+16.3 %** | +18.1 % [+15.0, +21.3] |
| | | SL(2,89)×Z_12 | 8,458,560 | 0.796 | 12.5 | 10.7 | **failed** (best 1 after 74,777 evals, 900 s) | | | |
| (15,9) | 168,016,334 | SL(2,449) | 90,518,400 | 0.740 | 2.1 | 8.0 | solved, 17 evals | 181,036,800 | +7.7 % | |
| | | **SL(2,457)** | 95,443,536 | 0.780 | 5.6 | 8.0 | solved, 209 evals, 91 s | **190,887,072** | **+13.6 %** | +15.9 % [+13.4, +18.6] |
| | | SL(2,461) | 97,971,720 | 0.801 | 8.8 | 7.9 | **failed** (best 2 after 4,761 evals, 2,404 s) | | | |
| (16,9) | 288,939,118 | **SL(2,541)** | 158,339,880 | 0.773 | 4.7 | 7.5 | solved, 25 evals, 41 s | **316,679,760** | **+9.6 %** | +12.5 % [+10.1, +15.0] |
| | | SL(2,547) | 163,666,776 | 0.799 | 8.5 | 7.5 | stopped (memory pressure on the box) at cost 2 after 449 evals, 888 s | | | |

**The rule "solves iff μ ≤ μ\*(N)" was right on every run above.** The solved runs had μ between 0.3 and 9.2, at or
below μ\*. The failures had μ above μ\*: 12.5 > 10.7 at (15,8), 8.8 > 7.9 at (15,9), and 8.5 > 7.5 at (16,9) (stopped early). The achieved orders land inside the ±2σ bands, or just below them
where we did not push further ((15,9), (16,9)). The (15,8) table value equals the (14,8) one (14,172,480). That is legal
(a Δ = 14 graph also has max degree ≤ 15), but suspicious, so recheck that cell against the wiki before announcing it.

Verification: haar_gen3's own full BFS check passed for all. **build_haar2.py VALID** for (15,8) 16,483,200
(sha256 3aee39eb66e87753f11873bbabc04fe4b163622f4c061cd7e2759c3ffde67ef9, 30 s, 2.6 GB), (12,9) 32,772,096
(sha256 7acac22b1f4c50404df2a86c8887c416fe94f829b231ca3694e71c9fb708a4c1, 73 s, 3.3 GB) and (10,10) 57,868,272
(sha256 1a8fd889805939c50316a84d2e651fd48d0c5a5c95ce716887f578135cdfc2c6, 852 s, 3.6 GB); (13,9) 62,156,160 (sha256 4fa150abcc58d8a9294e6a880f56f4c925a0830bf0ca71a7d4380109115c8e24, 103 s, 4.3 GB). build_haar2 is
too heavy for 111–317 M vertices on this shared box, so I also wrote an independent low-memory checker for SL(2,p)×Z_n, p prime: own element indexing, explicit matrix products, bitset BFS from (e,A) and (e,B), about
4N bits of memory. It agrees with build_haar2 on the cells both can check and rejects a corrupted file. The lab's check_haar_indep.py
also gives VALID for (15,8), (12,9), (10,10) and (13,9) (up to 1,562 s and 5.6 GB). Its results:
**VALID for all seven** ((15,8), (12,9), (10,10), (13,9), (14,9), (15,9), (16,9): both eccentricities ≤ D, every vertex reached, Δ distinct generators; 1.5–31 s, ≤ 120 MB). These graphs are **not harvested**. The solution files are in Appendix A. Harvest (labctl: build_haar2
or a C checker, check_haar_indep, bigcheck) is the coordinator's step.

### 3.3 Every cell D ∈ {5, 7, 8, 9, 10}, Δ ≤ 16

"ours" = research-lab/records.json as of 2b50d7f0c (before this session's cells). "pred vs table" = predicted 2N over
table. Verdict: "should beat" if the whole ±2σ band is above the table, "can't" if the whole band is below it.

**D = 5**

| Δ | table | ours | predicted Haar 2N [±2σ] | ceiling 2N_h | pred vs table | table/2N_h | verdict |
|---|---|---|---|---|---|---|---|
| 4 | 160 | 162 | 236 [198–242] | 158 | +47.7% | 1.00 | small-N: model not valid; ours |
| 5 | 336 | 354 | 412 [360–478] | 354 | +22.9% | 0.95 | small-N: model not valid; ours |
| 6 | 684 | – | 696 [622–786] | 684 | +2.0% | 1.00 | small-N: model not valid |
| 7 | 1,134 | 1,152 | 1,120 [1,016–1,244] | 1,198 | -1.1% | 0.95 | marginal; ours |
| 8 | 1,710 | 1,764 | 1,720 [1,578–1,888] | 1,948 | +0.7% | 0.88 | marginal; ours |
| 9 | 2,496 | 2,662 | 2,536 [2,344–2,758] | 2,994 | +1.7% | 0.83 | marginal; ours |
| 10 | 4,000 | – | 3,612 [3,356–3,902] | 4,402 | -9.7% | 0.91 | Haar can't (with current search) |
| 11 | 5,850 | – | 4,992 [4,662–5,368] | 6,238 | -14.6% | 0.94 | Haar can't (with current search) |
| 12 | 8,200 | – | 6,730 [6,308–7,206] | 8,576 | -17.9% | 0.96 | Haar can't (with current search) |
| 13 | 11,480 | – | 8,876 [8,348–9,470] | 11,500 | -22.7% | 1.00 | Haar can't (with current search) |
| 14 | 14,760 | – | 11,488 [10,834–12,222] | 15,090 | -22.2% | 0.98 | Haar can't (with current search) |
| 15 | 20,496 | – | 14,626 [13,822–15,518] | 19,438 | -28.6% | 1.05 | Haar can't (with current search) |
| 16 | 27,300 | – | 18,350 [17,378–19,428] | 24,634 | -32.8% | 1.11 | Haar can't (with current search) |

**D = 7**

| Δ | table | ours | predicted Haar 2N [±2σ] | ceiling 2N_h | pred vs table | table/2N_h | verdict |
|---|---|---|---|---|---|---|---|
| 3 | 168 | – | 240 [202–254] | 146 | +44.0% | 1.15 | small-N: model not valid |
| 4 | 840 | – | 876 [788–980] | 780 | +4.3% | 1.07 | small-N: model not valid |
| 5 | 3,110 | – | 2,856 [2,644–3,100] | 2,950 | -8.1% | 1.05 | small-N: model not valid |
| 6 | 8,310 | – | 7,872 [7,394–8,410] | 8,746 | -5.3% | 0.95 | marginal |
| 7 | 23,436 | – | 18,846 [17,850–19,948] | 21,856 | -19.6% | 1.07 | Haar can't (with current search) |
| 8 | 40,586 | – | 40,384 [38,474–42,480] | 48,172 | -0.5% | 0.84 | marginal |
| 9 | 117,648 | – | 79,306 [75,870–83,046] | 96,504 | -32.6% | 1.22 | Haar can't (with current search) |
| 10 | 224,694 | – | 145,210 [139,358–151,542] | 179,342 | -35.4% | 1.25 | Haar can't (with current search) |
| 11 | 398,580 | – | 251,110 [241,592–261,360] | 313,722 | -37.0% | 1.27 | Haar can't (with current search) |
| 12 | 664,300 | – | 414,118 [399,234–430,090] | 522,154 | -37.7% | 1.27 | Haar can't (with current search) |
| 13 | 1,062,936 | – | 656,192 [633,674–680,278] | 833,626 | -38.3% | 1.28 | Haar can't (with current search) |
| 14 | 1,771,560 | – | 1,004,916 [971,822–1,040,222] | 1,284,682 | -43.3% | 1.38 | Haar can't (with current search) |
| 15 | 2,480,184 | – | 1,494,350 [1,446,916–1,544,838] | 1,920,570 | -39.7% | 1.29 | Haar can't (with current search) |
| 16 | 4,022,340 | – | 2,165,922 [2,099,418–2,236,568] | 2,796,456 | -46.2% | 1.44 | Haar can't (with current search) |

**D = 8**

| Δ | table | ours | predicted Haar 2N [±2σ] | ceiling 2N_h | pred vs table | table/2N_h | verdict |
|---|---|---|---|---|---|---|---|
| 3 | 256 | – | 348 [300–408] | 240 | +36.3% | 1.07 | small-N: model not valid |
| 4 | 2,184 | – | 1,936 [1,780–2,118] | 1,860 | -11.3% | 1.17 | small-N: model not valid |
| 5 | 9,234 | – | 8,626 [8,110–9,206] | 9,292 | -6.6% | 0.99 | Haar can't (with current search) |
| 6 | 29,790 | 30,576 | 30,184 [28,698–31,820] | 34,370 | +1.3% | 0.87 | marginal; ours |
| 7 | 80,940 | 88,920 | 87,624 [83,874–91,702] | 103,046 | +8.3% | 0.79 | Haar should beat it; ours |
| 8 | 201,480 | 225,792 | 220,748 [212,264–229,898] | 265,130 | +9.6% | 0.76 | Haar should beat it; ours |
| 9 | 449,480 | 497,904 | 498,322 [480,746–517,158] | 607,456 | +10.9% | 0.74 | Haar should beat it; ours |
| 10 | 1,176,480 | – | 1,031,214 [997,336–1,067,350] | 1,270,992 | -12.3% | 0.93 | Haar can't (with current search) |
| 11 | 2,246,940 | – | 1,988,826 [1,927,298–2,054,216] | 2,472,270 | -11.5% | 0.91 | Haar can't (with current search) |
| 12 | 4,650,100 | – | 3,619,136 [3,512,820–3,731,784] | 4,529,596 | -22.2% | 1.03 | Haar can't (with current search) |
| 13 | 5,314,680 | 6,408,480 | 6,272,614 [6,096,510–6,458,738] | 7,894,402 | +18.0% | 0.67 | Haar should beat it; ours |
| 14 | 14,172,480 | – | 10,430,374 [10,149,060–10,727,058] | 13,188,182 | -26.4% | 1.07 | Haar can't (with current search) |
| 15 | 14,172,480 | – | 16,736,792 [16,301,316–17,195,212] | 21,245,378 | +18.1% | 0.67 | Haar should beat it |
| 16 | 36,201,060 | – | 26,036,916 [25,381,082–26,726,190] | 33,162,608 | -28.1% | 1.09 | Haar can't (with current search) |

**D = 9**

| Δ | table | ours | predicted Haar 2N [±2σ] | ceiling 2N_h | pred vs table | table/2N_h | verdict |
|---|---|---|---|---|---|---|---|
| 3 | 506 | – | 528 [468–604] | 402 | +4.6% | 1.26 | small-N: model not valid |
| 4 | 4,970 | – | 4,532 [4,228–4,880] | 4,574 | -8.8% | 1.09 | small-N: model not valid |
| 5 | 27,936 | – | 27,460 [26,088–28,970] | 30,372 | -1.7% | 0.92 | marginal |
| 6 | 117,360 | 121,440 | 121,542 [116,540–126,962] | 140,408 | +3.6% | 0.84 | marginal; ours |
| 7 | 400,160 | 416,640 | 426,784 [411,492–443,190] | 505,562 | +6.7% | 0.79 | Haar should beat it; ours |
| 8 | 1,091,232 | 1,245,312 | 1,261,560 [1,220,888–1,304,894] | 1,519,000 | +15.6% | 0.72 | Haar should beat it; ours |
| 9 | 2,961,536 | 3,290,112 | 3,268,794 [3,171,938–3,371,468] | 3,981,180 | +10.4% | 0.74 | Haar should beat it; ours |
| 10 | 7,057,400 | 7,488,000 | 7,635,822 [7,424,788–7,858,674] | 9,379,312 | +8.2% | 0.75 | Haar should beat it; ours |
| 11 | 15,200,448 | 16,369,920 | 16,408,246 [15,980,684–16,858,366] | 20,287,510 | +7.9% | 0.75 | Haar should beat it; ours |
| 12 | 30,001,152 | – | 32,920,114 [32,104,716–33,776,388] | 40,916,700 | +9.7% | 0.73 | Haar should beat it |
| 13 | 50,990,610 | – | 62,364,940 [60,887,274–63,913,436] | 77,845,988 | +22.3% | 0.66 | Haar should beat it |
| 14 | 95,087,738 | – | 112,533,952 [109,970,378–115,215,628] | 140,969,864 | +18.3% | 0.67 | Haar should beat it |
| 15 | 168,016,334 | – | 194,750,018 [190,466,944–199,223,528] | 244,698,146 | +15.9% | 0.69 | Haar should beat it |
| 16 | 288,939,118 | – | 325,027,598 [318,102,982–332,250,378] | 409,448,150 | +12.5% | 0.71 | Haar should beat it |

**D = 10**

| Δ | table | ours | predicted Haar 2N [±2σ] | ceiling 2N_h | pred vs table | table/2N_h | verdict |
|---|---|---|---|---|---|---|---|
| 3 | 800 | – | 836 [752–938] | 686 | +4.6% | 1.16 | small-N: model not valid |
| 4 | 11,748 | – | 11,052 [10,418–11,762] | 11,542 | -5.9% | 1.02 | small-N: model not valid |
| 5 | 90,068 | – | 90,712 [86,846–94,914] | 102,084 | +0.7% | 0.88 | marginal |
| 6 | 452,032 | 506,160 | 506,630 [488,790–525,746] | 590,400 | +12.1% | 0.77 | Haar should beat it; ours |
| 7 | 1,987,380 | 2,147,040 | 2,148,000 [2,081,998–2,218,114] | 2,553,816 | +8.1% | 0.78 | Haar should beat it; ours |
| 8 | 6,927,210 | 7,349,616 | 7,440,308 [7,234,252–7,657,924] | 8,961,488 | +7.4% | 0.77 | Haar should beat it; ours |
| 9 | 20,017,260 | 22,178,688 | 22,105,676 [21,542,202–22,698,226] | 26,868,404 | +10.4% | 0.75 | Haar should beat it; ours |
| 10 | 50,331,156 | – | 58,244,996 [56,858,510–59,698,256] | 71,272,556 | +15.7% | 0.71 | Haar should beat it |
| 11 | unreadable | – | 139,361,456 [136,230,462–142,634,688] | 171,421,158 | – | – | table value unreadable |
| 12 | 300,383,050 | – | 308,105,768 [301,520,162–314,975,880] | 380,557,116 | +2.6% | 0.79 | Haar should beat it |
| 13 | 617,330,936 | – | 637,700,106 [624,651,192–651,288,490] | 790,322,804 | +3.3% | 0.78 | Haar should beat it |
| 14 | 1,213,477,190 | – | 1,248,190,034 [1,223,616,968–1,273,740,182] | 1,551,284,138 | +2.9% | 0.78 | Haar should beat it |
| 15 | 2,300,326,510 | – | 2,328,881,322 [2,284,591,506–2,374,871,842] | 2,901,303,672 | +1.2% | 0.79 | marginal |
| 16 | 4,119,507,330 | – | 4,168,541,164 [4,091,703,740–4,248,237,626] | 5,203,776,338 | +1.2% | 0.79 | marginal |

### 3.4 Ranking

**Where a Haar search should beat the table (predicted gain at the predicted order):**
(13,9) +22 % ✓ (+21.9 %) · (14,9) +18 % ✓ (+17.2 %) · (15,8) +18 % ✓ (+16.3 %) · (15,9) +16 % ✓ (+13.6 %) · (10,10) +16 % ✓ (+15.0 %) ·
(16,9) +12.5 % ✓ (+9.6 %) · (12,9) +9.7 % ✓ (+9.2 %) · then the cells we already hold (+7–18 % predicted, all at the
prediction within ±2.5 %, so no slack left there without a new idea) · (12,10)–(14,10) +2.6–3.3 %
(N = 150–620 M: needs the low-memory checker and hours per run) · (15,10), (16,10) +1 % (marginal; N ≈ 1.2–2 G, out of
reach on this box).

**Marginal (band straddles the table):** (6,9) +3.6 %, (6,8) +1.3 %, (5,10) +0.7 %, (8,7) −0.5 %, (5,9) −1.7 %, (6,7) −5 %,
and D = 5 at Δ = 6–9 (small-N regime; our D = 5 records sit at the ceiling).

**Where Haar can't (with this machinery):** D = 5 at Δ ≥ 10 (−10 to −33 %), D = 7 at Δ = 7 and Δ ≥ 9 (−20 to −46 %), (10,8) −12 %,
(11,8) −12 %, (12,8) −22 %, (14,8) −26 %, (16,8) −28 %, (5,8) −7 %. In many of these the **table is above the
first-moment ceiling N_h**: D = 7 with Δ ≥ 9 (table/2N_h = 1.22–1.44), (12,8) 1.03, (14,8) 1.07, (16,8) 1.09, D = 5 with
Δ ≥ 13. Those graphs (Loz–Pérez-Rosés–Pineda-Villavicencio lifts and older structured constructions) beat random-like
covering. No random-like Haar graph should match them.

### 3.5 The three cells asked about

- **Δ10·D10:** table 50,331,156 needs N > 25.17 M. Predicted 58.2 M vertices (+15.7 %). Done: 57,868,272 (SL(2,307)),
  build_haar2 VALID and C-checker VALID. The next orders up (μ > μ\*) are predicted to fail. A product like
  SL(2,7)×SL(2,23)×Z_7 (57.1 M vertices) is a second family near this order.
- **Δ12·D9:** table 30,001,152 needs N > 15.0 M. Predicted 32.9 M (+9.7 %). Done: 32,772,096 (SL(2,127)×Z_8),
  build_haar2 VALID.
- **Δ13·D9:** table 50,990,610 needs N > 25.5 M. Predicted 62.4 M (+22.3 %). Done: 62,156,160 (SL(2,109)×Z_24), build_haar2 VALID and C-checker VALID.
  At the table's order, random S is already valid (μ = 0.3), so this table value is very weak.

## 4. Walls, and what could move them

### 4.1 Walls are where μ crosses the search capability

Capability at (7,8) (haar_gen3, K = 8, 90 s ≈ 4.5 M evaluations per run, 4 seeds per order):

| group | N | N/N_h | μ | solved | time to solve (s) | best when not solved |
|---|---|---|---|---|---|---|
| PSL(2,17)×Z_17 | 41,616 | 0.808 | 13.0 | 4/4 | 0.6, 0.8, 2.7, 4.6 | |
| SL(2,13)×Z_19 | 41,496 | 0.805 | 12.7 | 4/4 | 0.4, 1.3, 4.1, 11.3 | |
| PSL(2,17)×Z_18 | 44,064 | 0.855 | 21.5 | 2/4 | 25.8, 30.2 | 1, 2 |
| SL(2,13)×Z_20 | 43,680 | 0.848 | 20.0 | 1/4 | 8.3 | 1, 1, 2 |
| PSL(2,17)×Z_19 | 46,512 | 0.903 | 34.0 | 0/4 | | 3, 3, 5, 6 |
| SL(2,13)×Z_21 | 45,864 | 0.890 | 30.2 | 0/4 | | 3, 5, 5, 6 |

From μ = 13 (median ~10^5 evaluations) to μ ≈ 21 (~5·10^6), the cost grows ~50× for Δμ ≈ 8. Evaluations to solve go
roughly like e^(μ/2), i.e. **μ_max(M) ≈ 13 + 2 ln(M/10^5)** for M evaluations. The same rule fits the big cells: with
~10^4 evaluations it gives μ_max ≈ 8.4. The big cells solved at μ = 8.3–9.2 and failed at 12.5. For comparison, random
sampling would need ~e^(εμ) ≈ e^(2μ) samples, so annealing with targeted moves is much better than sampling. But its
cost is still exponential in μ.

Gain per compute: d ln N = d ln μ\*/(W/N − 1). Ten times the evaluations adds ≈ 4.6 to μ\*. At μ\* ≈ 10–20 and
W/N ≈ 8–13, that is **+3–4 % in N per 10× compute**. Reaching N_h needs μ ≈ Δ ln N ≈ 70–200, i.e. e^(30–90) times more
search. **So the walls are fundamental for annealing over random-like S.** They are not mathematical barriers. The
first-moment ceiling suggests good S exist up to ~N_h (≈ 1.2× the walls), but finding them by search is hopeless.

### 4.2 What does not help (tested or ruled out)

- **Better word counts.** Short-cycle losses are < 0.2 % of W (§2.3.1). There is nothing to gain from girth.
- **Balancing the Z_n fibers.** Already perfect: the Jensen excess is 1.000 (§2.3.3).
- **Parity tricks for odd D.** They are already neutral (§2.3.4).
- **Symmetric S (an orbit of an automorphism).** Idea: S = {e} ∪ {α^i(s)} with α ∈ Aut(G) of order Δ−1 (conjugation by g
  on Q, z ↦ rz on Z_n). The ball is α-invariant, so uncovered elements come in orbits of size Δ−1. In an ideal Poisson
  model, exhaustive search over s (only N choices) would reach N_h. Implemented as an ORBIT mode in a haar_gen3 copy and
  tested at (8,8) on SL(2,49), SL(2,8)×Z_239, SL(2,8)×Z_211, SL(2,7)×Z_337, PGL(2,7)×Z_337, PSL(2,13)×Z_98/113 and
  PSL(2,29)×Z_9 (10^4–5·10^5 samples each). The result was **worse than annealing every time:**
  - Pure conjugation in SL(2,q): typical cost ~2·10^4 and best 282 against random-S minimum 14. S lies in one conjugacy
    class; my guess (not checked) is that the words' class distribution is badly skewed.
  - Automorphisms acting trivially on a quotient (r ≡ 1 mod 7 on Z_49 ⊂ Z_98; r = 1 on Z_9; no e and a Z_2 quotient)
    leave 50–60 % of G uncovered.
  - Even in the best families there is a hard floor. SL(2,8)×Z_211 hit cost exactly 9 (one orbit of 7 plus 2 α-fixed
    points) 9,485 times in 338,793 samples and never lower, while annealing reached 6. The orbit space is small: the s
    choices collapse to few classes, and α-fixed points are covered only with probability 1 − e^(−W/((Δ−1)N)).
  Verdict: dead in this form.

### 4.3 What could beat C_D

The model says any random-like S loses the factor ln(N/μ\*) to coupon collecting. Beating C_D needs S whose last-level
words hit the remaining elements with *negative* correlation, like a covering design rather than random darts. The proof
that this is possible is in the table itself. Perfect difference sets (Singer) are Haar graphs with zero waste at D = 3
(N = W). And the cells listed in §3.4 have tables *above* the random ceiling N_h, built by voltage lifts over larger
base graphs. For D ≥ 7 no generalized polygons exist (Feit–Higman), so there is no ready-made zero-waste structure.

### 4.4 Proposed search change, with estimated gain

**Change the job planner from "N/N_h ≤ 0.85" to "μ(N) ≤ μ_max(M)".** Here μ(N) = N e^(−W/N) is computed exactly per
order, and μ_max(M) = 13 + 2 ln(M/10^5) for a budget of M evaluations. M = seconds per run / (seconds per evaluation),
and seconds per evaluation is ≈ (1–2)·10^(−9)·N·(#BFS) on this Mac for N ≳ 10^7 (one BFS for even D, two for odd D). Rank all open cells by predicted gain
2N_pred/table − 1, and run the largest-gain cells first.
- **Estimated gain.** In the untried big cells the gain is the predicted +10 % to +22 %. Today it delivered +9.2 % to
  +21.9 % in seven cells. (15,9) and (16,9) have 2–3 % headroom left. In cells we already hold, it saves wasted runs above the wall. It cannot add more than the
  3–4 % per 10× compute of §4.1. Choosing groups with lower ε (screening, as now) is worth up to ~ln(ε_old/ε_new)/(W/N)
  ≈ 2–4 %.
- **The genuinely new direction for the held cells** is a different object: lifts over a base graph with more than 2
  vertices, where the base supplies the structure of §4.3. That is outside this session's scope. I did not test it.

## 5. Theorem direction (honest status)

**Proved (elementary):**
- (a) The covering lemma of §2.1 (D even: one condition; D odd: two, each inverse-closed). It is already in d5/REPORT.md
  and PLAN.md §2.
- (b) The Haar counting ceiling: N ≤ W(Δ,D), so C_D ≤ Δ g_Δ for every group and every S. For D even this is
  2N ≤ 2Δ Σ_{i<k}(Δ−1)^(2i), slightly below the bipartite Moore bound.
- (c) The identity C_D = Δ g_Δ /ln(N/μ) (exact, with μ := N e^(−W/N) as a definition). The content is entirely in the
  empirical fact that μ at the records stays in a narrow band (9–40).

**Heuristic (well supported, not proved):**
- (d) The Poisson model and the threshold N ≈ W/ln(N/μ\*).
- (e) The factor-2 advantage of Haar over random bipartite graphs.
- (f) N_h as the true ceiling for random-like S.

**What a theorem would look like:**
- (g) *Conjecture (sharp threshold for random Haar graphs of SL(2,q)).* Fix Δ ≥ 3. Let S be uniform random of size Δ in
  G = SL(2,q), N = |G|, q → ∞, and let D = D(q) satisfy N e^(−W(Δ,D)/N) → μ ∈ [0, ∞). Then P(diam H(G,S) ≤ D) → e^(−cμ),
  with c = 1 for both parities (for odd D, counting inverse pairs as one target, §2.3.4). This would give |V| = (2 − o(1)) Δ g (Δ−1)^(D−2)/ln N for infinitely many D.
  - What it needs: Poisson convergence of the number of uncovered elements. By the moment method that requires (i) each
    fixed reduced word of length ~log N to be equidistributed on G, and (ii) pairs (w₁, w₂) of distinct such words to be
    jointly equidistributed on G², with errors summable over ~W² pairs.
  - (i) For fixed words this is known: word maps on SL(2,q) are almost uniform (Larsen–Shalev type results; check exact
    statements).
  - (ii) For words of length growing like log N, uniformly over all W² pairs, this is far beyond Bourgain–Gamburd, which
    gives mixing only in C·log N steps with C large.
  - **Not within reach in a session, and I would not claim progress on it.**
- (h) *Within reach, but weaker.* The analogous statement for random bipartite Δ-regular graphs (the union of Δ random
  perfect matchings): |V| ≥ (1 − o(1)) Δ g (Δ−1)^(D−2)/ln N, i.e. half of the Haar law. I expect it is provable with standard
  configuration-model methods (Bollobás–Fernandez de la Vega style). This is probably known or a routine exercise, so it
  is not new, and it is weaker than our computer records.
- (i) *Kenaznia's version* (an explicit family with |V| ≥ c (Δ−1)^(D−2), c constant, all large D) conflicts with the
  law: random-like constructions give c_D ~ Δ/(D ln(Δ−1)) → 0. It could only hold via structured S that beat coupon
  collecting at every D, and no such mechanism is known for D ≥ 7. The "sharper constant for even vs odd D" is answered
  negatively by §2.3.5.

## 6. Verified versus guessed

- **Verified by computation here:**
  - All fits and numbers in §1, from the solution files and `size_law_fits.csv`.
  - The ball-growth, excess, inverse-pair, Z_n-fiber, parity and capability measurements of §2.3 and §4.1.
  - The ORBIT-mode experiments.
  - The seven new-cell runs: haar_gen3 internal full check for all; build_haar2 and check_haar_indep VALID for (15,8), (12,9), (10,10)
    and (13,9); the independent C checker as listed in §3.2.
- **Fitted, so it can be wrong out of range:** μ\*(N) (calibrated on N ≤ 11 M; tested today up to 158 M), the D = 7
  predictions (no D = 7 Haar data) and the 13 + 2 ln(M/10^5) capability rule (one cell, 24 runs).
- **From memory, not re-checked:** Bollobás–Fernandez de la Vega, Lubetzky–Peres, Sardari, Larsen–Shalev and
  Bourgain–Gamburd statements as summarised in §2.4 and §5.
- **Guessed:** that structured lifts over bigger bases are the way past C_D (§4.3–4.4).

## 7. Reproduction

Session scripts are committed in `research/frontier/sizelaw/` (with a README). They were developed in the session scratchpad
`/private/tmp/claude-502/-Users-dogaozden-AI-Projects-degree-diameter/31a2fcff-fd6b-4c01-b1b7-05c9b8d9f143/scratchpad/sl/` (temporary: /private/tmp does not survive a reboot). Ask if they should go into
`research/frontier/`. They are:
- `data.py`, `fit.py` (§1 and the CSV), `predict.py` and `table_md.py` (§3), `zbal.py` (fiber loads);
- `haar_orb.c` (haar_gen3 plus ORBIT mode, DUMPUNC, LEVELS and a mean/variance line in RANDSAMPLE);
- `cap/` (capability runs) and `big/` (new-cell runs, logs and verifier outputs).

The low-memory checker `haarcheck_sl.c` is reproduced in Appendix B, because harvesting the 111–317 M-vertex graphs
needs it. Build it with `cc -O3 -o haarcheck_sl haarcheck_sl.c` and run `./haarcheck_sl SOL.txt`.

The formulas are all in this file. W and N_h are as in heuristic.py, μ = N e^(−W/N), and the prediction solves
ln N − W/N = 4.335 − 0.123 ln N.

## 8. Planning by μ (for watchers' job lists)

Use this recipe for every new job list (`sizelaw/plan_mu.py` does steps 1–3).
1. **Window.** LO = table/2 + 1 (or our best + 1). HI = the order where μ reaches the limit in step 3.
2. **μ for each candidate order.** μ(N) = N e^(−W(Δ,D)/N), with W as in heuristic.py. It depends only on N, not on the
   group.
3. **Limit for the job's budget.** M = job seconds / t_eval, where t_eval ≈ c·N·b, b = 1 (even D) or 2 (odd D),
   c ≈ 1.5·10^(−9) s for N ≥ 10^7 and ≈ 4.5·10^(−10) s below (this Mac; cloud cores are about 1.5–2× slower).
   μ_max = max(13 + 2 ln(M/10^5), μ\*(N)) with ln μ\*(N) = 4.335 − 0.123 ln N. The first rule comes from long runs at
   small N; the second from 10–40 minute runs on SL(2,q) × small Z_n at N ≥ 10^6. Both are rough, about ±2 in μ.
4. **Classify each order:**
   - μ ≤ μ_max − 2: safe. One seed usually solves it within the budget. Put these first so the cell is taken.
   - μ_max − 2 < μ ≤ μ_max + 1: stretch. Use 2–4 seeds and the best-screened groups.
   - μ > μ_max + 2: skip. More seeds do not help much: each +1 in μ costs about e^(1/2) ≈ 1.6× more evaluations.
5. **Group choice.** Screen with `RANDSAMPLE=300 haar_gen3 …` and keep groups with the smallest median/μ. For
   N ≥ 10^6, SL(2,q) × Z_n with n ≤ 12 and SL × SL products are the reliable families. For N ≤ 10^4, the metacyclic
   `meta m k r` groups screen best. Avoid simple groups alone and large cyclic factors.
6. **Memory.** haar_gen3 needs about 14 bytes per group element plus 12·q³ bytes for SL(2,q). That is 2.3 GB at
   N = 158 M (q = 541) and about 4.5 GB at N = 600 M (q ≈ 400–450, n ≈ 7–9). Prefer smaller q with a larger n when
   memory is tight. The harvest checks up to ~60 M vertices with build_haar2 (≤ 6 GB). Above that, use
   `sizelaw/haarcheck_sl.c` (4N bits; SL(2,p) × Z_n only) plus a second checker.
7. **Order.** Start with the safest order above the table (claims the cell). Then step up by about +1 in μ per job,
   until two seeds fail at the same μ.

How well the rule did, over the 19 big-cell runs (N ≥ 7 M) of both sessions:
- All 15 runs with μ ≤ μ\*(N) solved.
- Of the 4 runs with μ between μ\* + 0.9 and μ\* + 1.8, one solved ((12,10) at μ\* + 1.2) and three failed ((15,8)
  +1.8, (15,9) +0.9 and (16,9) +1.0; the last was stopped early).
- At D = 7, (8,7) solved at μ = 25.5 after 4.3·10^7 evaluations, where the M-rule gives μ_max = 25.1. Two other seeds,
  and two groups at μ 24.4–25.0, were still at cost 2–8 after 5·10^7 evaluations.

## 9. Wave 4: the remaining open cells at D ≥ 7 (2026-10-23, second session)

μ at the table value (that is, at N = table/2 + 1) says which cells a Haar search can take. The limit μ_max is from §8.

| cell | table | μ at table | μ_max (local budget) | table/2N_h | verdict | result |
|---|---|---|---|---|---|---|
| (3,7) | 168 | 19 | ~30 | 1.16 | above the first-moment ceiling | 59 groups of order 85–100 × 10 s: best cost 10. Not taken |
| (4,7) | 840 | 31 | ~33 (10^9 evals) | 1.08 | above the ceiling; long shot | best cost 4 after 10^9 evals (meta 44 10 3, 600 s); wave4 list |
| (5,7) | 3,110 | 47 | ~30 | 1.05 | can't | not run |
| (6,7) | 8,310 | 38 | ~30 (1 h) | 0.95 | long shot | best cost 2 (meta 279 15 7, N = 4,185); wave4 lists |
| (7,7) | 23,436 | 99 | ~27 | 1.07 | can't | not run |
| **(8,7)** | 40,586 | 23 | ~25–28 | 0.84 | reachable | **41,040** (SL(2,19)×Z_3, +1.1 %), D7_PUSH |
| (9–16,7) | 117,648 – 4,022,340 | 360 – 10^4 | ~20 | 1.22–1.44 | can't (tables far above the ceiling) | not run |
| (10,8) | 1,176,480 | 63 | ~15 | 0.93 | can't | not run |
| (11,8) | 2,246,940 | 57 | ~14 | 0.91 | can't | not run |
| (12,8), (14,8), (16,8) | 4.65 M – 36.2 M | 230 – 733 | ~10–13 | 1.03–1.09 | can't | not run |
| **(12,10)** | 300,383,050 | 4.7 | 7.5–10 | 0.79 | reachable | **310,628,640** (SL(2,281)×Z_7, +3.4 %); also 300,799,200 and 306,179,328 |
| **(13,10)** | 617,330,936 | 3.7 | 7–9 | 0.78 | reachable | **636,550,992** (SL(2,307)×Z_11, +3.1 %); also 622,736,928 |
| **(14,10)** | 1,213,477,190 | 3.6 | 6–8 | 0.78 | reachable | **1,217,130,096** (SL(2,443)×Z_7, +0.3 %), D14_PUSH |
| (15,10), (16,10) | 2.30 G, 4.12 G | ~3 | ~6 | 0.79 | marginal (+1 % predicted) | not run: N > 2^30 overflows haar_gen3's 32-bit indices, and ~16–30 GB RAM needed |
| (6,5) | 684 | 35 | ~37 | 1.00 | at the ceiling; the earlier D = 5 hunts reached cost 2 | not run |
| (10,5) | 4,000 | 50 | ~30 | 0.91 | can't | not run |

Notes:
- **D = 7 calibration.** The four (8,7) groups at μ 24.4–25.5 behaved as §8 predicts (one solve at 4.3·10^7 evaluations,
  the rest at cost 2–8). Random-S excess at D = 7 is larger than at D ≥ 8: median cost/(2μ) = 1.4–3 for the matrix
  groups, because q is small. For N ≤ 5,000 the metacyclic groups screen best (random-S minimum cost 4–24 at μ 34–41).
  The model's D = 7 column (interpolated in §3.3) stands: only (8,7) was reachable, plus long shots at (4,7) and (6,7).
- **Why D = 8 with Δ ≥ 10 is closed to Haar search.** At the table order, μ is 57–733. Each +1 in μ costs ~1.6× more
  evaluations, so even (11,8) needs ~e^((57−14)/2) ≈ 10^9 times today's budget. Those table graphs beat random-like
  covering (§3.4).
- **Verification.** All new graphs pass haar_gen3's own full BFS and `sizelaw/haarcheck_sl.c`. (8,7) also passes
  build_haar2 (sha256 0fc82859323f5e4ad9fff3610b3d3b3869ba891da4039e4242d04b0779080cab). The D = 10 graphs have
  0.3–1.2 G vertices, too big for the Python checkers on this box.
- **(15,8) table value.** Rechecked against TABLE.md's source: DS14v2 Table 4 (p. 37, downloaded again today and read
  with PDFKit) really lists 14,172,480 for both Δ = 14 and Δ = 15 at D = 8. The live CombinatoricsWiki page still fails
  TLS (certificate name mismatch); I did not bypass it. So TABLE.md is faithful to its source. Whether the wiki has a
  larger Δ = 15 value is unverified.
- **wave4 lists** (`research/frontier/wave4/`, wave3 format, one file per 4-core watcher):
  - `jobs4_d8D7_w1.txt`: (8,7) above 41,040, 7 groups × 4 seeds × 3600 s.
  - `jobs4_d6D7_w1.txt`, `jobs4_d6D7_w2.txt`: (6,7), 16 groups × 2 seeds × 3600 s each list.
  - `jobs4_d4D7_w1.txt`: (4,7), 8 groups × 4 seeds × 1800 s.
  - All jobs need under 10 MB. (6,7) and (4,7) are long shots by the μ rule; (8,7) is a stretch.

## Appendix A. Solution files of the new cells (haar_gen3 format; build_haar2.py and check_haar_indep.py read them)

`d10D10_sl_307_1_s3.txt` — (10,10), 57,868,272 vertices

```
10 10 sl 307 n 1 N 28934136
93942 mat(1,0,0,1) z=0
824950 mat(8,232,41,153) z=0
14408044 mat(152,268,227,273) z=0
9847528 mat(104,149,196,24) z=0
15655941 mat(166,35,169,154) z=0
28024692 mat(297,107,197,41) z=0
19456381 mat(206,134,256,171) z=0
4057604 mat(43,16,292,23) z=0
19002313 mat(201,190,241,266) z=0
995382 mat(10,173,88,141) z=0
```

`d12D9_sl_127_8_s2.txt` — (12,9), 32,772,096 vertices

```
12 9 sl 127 n 8 N 16386048
128016 mat(1,0,0,1) z=0
1986015 mat(15,50,93,73) z=7
15824548 mat(122,82,43,82) z=4
1464068 mat(11,45,1,85) z=4
4852048 mat(37,77,81,21) z=0
729896 mat(5,84,51,95) z=0
7498335 mat(58,15,31,100) z=7
15996983 mat(123,125,7,35) z=7
5450207 mat(42,31,47,71) z=7
10951881 mat(84,112,52,89) z=1
12244172 mat(94,114,44,25) z=4
11126977 mat(86,30,95,11) z=1
```

`d13D9_sl_109_24_s2.txt` — (13,9), 62,156,160 vertices

```
13 9 sl 109 n 24 N 31078080
282528 mat(1,0,0,1) z=0
5009060 mat(17,62,84,82) z=20
21559725 mat(75,67,52,61) z=21
28950214 mat(101,58,64,40) z=22
5663079 mat(19,94,85,19) z=15
27351242 mat(95,101,40,15) z=2
25120771 mat(88,11,80,93) z=19
3608634 mat(12,72,48,61) z=18
8619607 mat(30,25,104,54) z=7
14831036 mat(52,2,38,100) z=20
29897651 mat(104,93,83,91) z=11
11065309 mat(38,88,93,6) z=13
17988651 mat(63,10,43,102) z=3
```

`d14D9_sl_191_8_s1.txt` — (14,9), 111,482,880 vertices

```
14 9 sl 191 n 8 N 55741440
290320 mat(1,0,0,1) z=0
25264125 mat(86,109,21,151) z=5
8713207 mat(29,164,68,187) z=7
6947904 mat(23,155,11,124) z=0
8052941 mat(27,114,47,57) z=5
26039545 mat(89,43,112,67) z=1
12099969 mat(41,88,158,41) z=1
20687786 mat(70,170,24,1) z=2
16822436 mat(57,123,85,36) z=4
36310792 mat(124,80,116,138) z=0
18412694 mat(63,18,36,77) z=6
16903284 mat(57,176,68,86) z=4
28967078 mat(99,49,97,185) z=6
24609906 mat(84,62,183,151) z=2
```

`d15D8_sl_101_8_s2.txt` — (15,8), 16,483,200 vertices

```
15 8 sl 101 n 8 N 8241600
80800 mat(1,0,0,1) z=0
4024051 mat(49,32,26,17) z=3
2421546 mat(29,68,97,22) z=2
7951138 mat(97,44,52,59) z=2
6725231 mat(82,42,30,24) z=7
6703713 mat(82,15,68,26) z=1
6685465 mat(81,94,9,94) z=1
4476142 mat(54,86,78,70) z=6
3175151 mat(38,92,64,46) z=7
3949763 mat(48,41,32,0) z=3
5881122 mat(72,7,62,86) z=2
4898462 mat(60,3,45,9) z=6
2690418 mat(32,98,73,50) z=2
292037 mat(3,59,43,38) z=5
7659744 mat(93,87,89,42) z=0
```

`d15D9_sl_457_1_s2.txt` — (15,9), 190,887,072 vertices

```
15 9 sl 457 n 1 N 95443536
208392 mat(1,0,0,1) z=0
27047740 mat(129,233,195,168) z=0
51568632 mat(246,420,295,212) z=0
67598112 mat(323,307,43,72) z=0
6289463 mat(30,53,229,39) z=0
71802037 mat(343,366,25,44) z=0
29033779 mat(139,9,112,50) z=0
19364602 mat(92,330,141,14) z=0
22058593 mat(105,284,117,286) z=0
91792412 mat(439,236,306,431) z=0
50938691 mat(243,413,100,390) z=0
15971965 mat(76,218,272,221) z=0
61508091 mat(294,234,4,412) z=0
4943419 mat(23,307,50,429) z=0
11188335 mat(53,262,61,86) z=0
```

`d16D9_sl_541_1_s1.txt` — (16,9), 316,679,760 vertices

```
16 9 sl 541 n 1 N 158339880
292140 mat(1,0,0,1) z=0
30128321 mat(102,509,31,282) z=0
95335254 mat(325,396,234,385) z=0
113922794 mat(389,130,96,135) z=0
48049040 mat(164,92,125,146) z=0
53779450 mat(183,405,263,180) z=0
104983757 mat(358,378,2,460) z=0
122522325 mat(418,336,432,157) z=0
94017273 mat(321,124,129,215) z=0
81245958 mat(277,321,201,22) z=0
28267814 mat(96,316,23,25) z=0
87233559 mat(298,28,14,152) z=0
4790596 mat(16,200,41,73) z=0
88366506 mat(301,499,107,305) z=0
21757624 mat(74,184,227,60) z=0
147153006 mat(502,420,465,0) z=0
```

## Appendix B. haarcheck_sl.c (independent low-memory checker, SL(2,p) × Z_n, p prime)

```c
/* haarcheck_sl: independent, low-memory diameter check of a Haar graph H(G,S), G = SL(2,p) x Z_n, p prime.
 * Reads a haar_gen3 solution file (header "d D sl p n NCYC N NTOT", then d lines "<idx> mat(a,b,c,d) z=Z"; only the
 * mat/z descriptions are used).  Vertices (g,A),(g,B); edges (g,A) ~ (s g, B).  Right multiplication by G is
 * transitive on each side, so BFS from (e,A) and from (e,B) give the exact diameter.
 * Own element indexing (keyed on c, unlike haar_gen3's a-keyed one): c != 0: (c,a,d) -> b = (ad-1)/c;
 * c = 0: a != 0, d = 1/a, b free.  Neighbours are computed by explicit 2x2 matrix products mod p.
 * Memory: 4 bitsets of N bits per BFS.  Usage: haarcheck_sl SOL.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static long long p, n, N;
static long long *INV;
static long long md(long long x) { x %= p; return x < 0 ? x + p : x; }
static long long enc(long long a, long long b, long long c, long long d, long long z) {
    long long k;
    if (c) k = ((c - 1) * p + a) * p + d;
    else k = (p - 1) * p * p + (a - 1) * p + b;
    return k * n + z;
}
static void dec(long long g, long long *a, long long *b, long long *c, long long *d, long long *z) {
    *z = g % n; long long k = g / n;
    if (k < (p - 1) * p * p) { *c = k / (p * p) + 1; *a = k / p % p; *d = k % p; *b = md((*a * *d - 1) % p * INV[*c]); }
    else { k -= (p - 1) * p * p; *c = 0; *a = k / p + 1; *b = k % p; *d = INV[*a]; }
}
typedef struct { long long a, b, c, d, z; } el;
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_sl SOL.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    int dg, D; char fam[64]; long long NN;
    if (sscanf(line, "%d %d %63s %lld n %lld N %lld", &dg, &D, fam, &p, &n, &NN) != 6 || strcmp(fam, "sl")) {
        fprintf(stderr, "only 'sl p' (p prime) headers: %s", line); return 2; }
    for (long long t = 2; t * t <= p; t++) if (p % t == 0) { fprintf(stderr, "p not prime\n"); return 2; }
    N = p * (p * p - 1) * n;
    if (N != NN) { fprintf(stderr, "header N %lld != p(p^2-1)n = %lld\n", NN, N); return 2; }
    INV = malloc(sizeof(long long) * p); INV[0] = 0;
    for (long long x = 1; x < p; x++) { long long r = 1, e = p - 2, bb = x; while (e) { if (e & 1) r = r * bb % p; bb = bb * bb % p; e >>= 1; } INV[x] = r; }
    el S[64], SI[64]; int k = 0;
    while (fgets(line, sizeof line, f) && k < 64) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        long long a, b, c, d, z; if (sscanf(m, "mat(%lld,%lld,%lld,%lld)", &a, &b, &c, &d) != 4 || sscanf(zz, "z=%lld", &z) != 1) return 2;
        if (md(a * d - b * c) != 1 || a < 0 || a >= p || b < 0 || b >= p || c < 0 || c >= p || d < 0 || d >= p || z < 0 || z >= n) { fprintf(stderr, "bad element: %s", line); return 2; }
        S[k] = (el){a, b, c, d, z}; SI[k] = (el){d, md(-b), md(-c), a, md(0) + (n - z) % n}; k++;
    }
    if (k != dg) { fprintf(stderr, "read %d elements, expected %d\n", k, dg); return 2; }
    for (int i = 0; i < k; i++) for (int j = 0; j < i; j++)
        if (!memcmp(&S[i], &S[j], sizeof(el))) { fprintf(stderr, "repeated generator %d %d\n", i, j); return 2; }
    /* self-test of enc/dec */
    for (long long g = 0; g < N; g += N / 1000 + 1) { long long a, b, c, d, z; dec(g, &a, &b, &c, &d, &z);
        if (md(a * d - b * c) != 1 || enc(a, b, c, d, z) != g) { fprintf(stderr, "index self-test failed\n"); return 2; } }
    long long W = (N + 63) / 64;
    uint64_t *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); cur[s] = calloc(W, 8); nxt[s] = calloc(W, 8); }
    int bad = 0;
    for (int start = 0; start < 2; start++) {
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(cur[s], 0, W * 8); }
        long long e = enc(1, 0, 0, 1, 0); vis[start][e >> 6] |= 1ULL << (e & 63); cur[start][e >> 6] |= 1ULL << (e & 63);
        long long reached[2] = {0, 0}; reached[start] = 1; int side = start, ecc = 0;
        for (int step = 1; step <= D; step++) {
            int ns = side ^ 1; long long add = 0; memset(nxt[ns], 0, W * 8);
            el *T = side == 0 ? S : SI;          /* (g,A) -> (s g, B);  (h,B) -> (s^-1 h, A) */
            for (long long w = 0; w < W; w++) { uint64_t bits = cur[side][w];
                while (bits) { int bt = __builtin_ctzll(bits); bits &= bits - 1; long long g = w * 64 + bt;
                    long long a, b, c, d, z; dec(g, &a, &b, &c, &d, &z);
                    for (int i = 0; i < k; i++) { const el *s = &T[i];
                        long long h = enc((s->a * a + s->b * c) % p, (s->a * b + s->b * d) % p, (s->c * a + s->d * c) % p, (s->c * b + s->d * d) % p, (s->z + z) % n);
                        uint64_t m1 = 1ULL << (h & 63);
                        if (!(vis[ns][h >> 6] & m1)) { vis[ns][h >> 6] |= m1; nxt[ns][h >> 6] |= m1; add++; } } } }
            memset(cur[side], 0, W * 8); uint64_t *t = cur[ns]; cur[ns] = nxt[ns]; nxt[ns] = t;
            reached[ns] += add; if (add) ecc = step; side = ns;
        }
        printf("from (e,%c): reached A %lld/%lld, B %lld/%lld within %d, ecc %d\n", start ? 'B' : 'A', reached[0], N, reached[1], N, D, ecc);
        if (reached[0] != N || reached[1] != N) bad = 1;
    }
    printf("%s d=%d D=%d group=sl %lld x Z_%lld N=%lld vertices=%lld (distinct generators, %d-regular simple)\n", bad ? "INVALID" : "VALID", dg, D, p, n, N, 2 * N, dg);
    return bad;
}
```
