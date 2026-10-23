# Data check: the threshold theorem against our records and against Monte Carlo

theory job "cd-theory", 2026-10-23. Scripts are in `scripts/`, run from that folder. Saved outputs: `*_out.txt`.
- `data_check.py`: records, per-D tables, μ fits.
- `data_check2.py`: Theorem 2 check, budget model, parity × family.
- `budget_loo.py`: leave-one-out for the budget model.
- `sim.py`, `sim2.py`: Monte Carlo; results in `sim_results.csv` and `sim2_results.csv`.
- `model.py`: the §3 Poisson model of THRESHOLD.md.

**Data.** 117 records in 31 cells (best per cell used unless stated):
- all 97 haar_gen/haar_gen3 files in `research/frontier/sols/` at this commit;
- the 18 D = 5 files in `research/d5/sols/`;
- the two D = 5 Haar graphs documented only in `d5/REPORT.md`.

That is 12 more cells than SIZE_LAW's 19-cell fit (§9's new cells are included). Group invariants (centre,
involutions, |G'|) come from class formulas, checked by brute force for SL, PSL and PGL(2,p), p ≤ 13
(`groups_inv.py`).

## 1. What the theorem predicts, in one line

At the threshold, ln N − W/N = ln μ, where μ is the Poisson mean of missed targets. For one random S,
μ ≈ ln(1/P(success)), e.g. ln 2 at a 50 % success rate. So the invariant is

  **C_D · ln(N/μ) / (Δ g_Δ) = 1**   (equivalently W/N = ln N − ln μ),

and **not** C_D · ln N = const. C_D·ln N/(Δ g_Δ) = 1/ρ with ρ := W/(N ln N); the theorem says ρ → 1 like
1 − ln μ/ln N.

## 2. Is C_D · ln N constant across D and Δ? No; the drift is exactly ln μ/ln N

Best record per cell:

| D | cells | C_D (mean) | C_D ln N/(Δ g_Δ) | ρ = W/(N ln N) | mean ln N | mean ln μ | 1 − ⟨ln μ⟩/⟨ln N⟩ |
|---|---|---|---|---|---|---|---|
| 5 | 4 | 2.65 | 2.30 | 0.44 | 6.4 | 3.54 | 0.44 |
| 7 | 2 | 1.28 | 1.64 | 0.62 | 9.1 | 3.46 | 0.62 |
| 8 | 6 | 1.00 | 1.33 | 0.76 | 12.6 | 2.87 | 0.77 |
| 9 | 11 | 0.83 | 1.19 | 0.85 | 15.5 | 2.26 | 0.85 |
| 10 | 8 | 0.68 | 1.17 | 0.86 | 16.7 | 2.20 | 0.87 |

- C_D·ln N is not constant: it falls from 2.3 to 1.17, in units of Δg_Δ. The same holds across Δ at fixed D:
  at D = 9, 1/ρ goes 1.37 (Δ = 6), 1.27, 1.24, 1.23, 1.17, 1.17, 1.15, 1.14, 1.13, 1.10, 1.09 (Δ = 16).
- The last two columns agree to ±0.01. So the whole drift of C_D·ln N is the ln μ/ln N term.
- ln μ itself varies little: 1.4–3.7, while ln N runs 5.2–20.2. That is the coupon-collector law with a slowly
  varying μ*, as SIZE_LAW §1.4 found.
- Kenan's hunch is confirmed: the log factor is the D-drift of C_D. C_D ≈ Δg/((D−2) ln(Δ−1) + ln C_D − ln μ*).

**Fits on 31 cells** (SIZE_LAW had 19):
- ln μ* = 4.58 − 0.144 ln N (se 0.13, 0.009), residual sd 0.205.
- Linear in μ: **μ* = 48.5 − 2.34 ln N (se 2.6, 0.18).**
- Parity residuals with the generic μ: even +0.063, odd −0.052. With the special-target μ of THRESHOLD §3:
  even +0.033, odd −0.027. The correction halves the remaining parity offset; it was already only 1.6σ.

## 3. "Best of T tries": does it account for the remaining drift? Yes, to 2 %

**Single random S.** By THRESHOLD Corollary 4.1 (and Conjecture 6 for fixed Δ), P(one random S works) ≈ e^{−μ}.
- SIZE_LAW §3.2 has the direct test. Every run at μ ≤ 1 succeeded within about 9 evaluations, i.e. essentially
  the first random S: (13,9) at μ = 0.3 "random S already valid"; (10,10) at μ = 0.8; (15,8) at μ = 1.0.
- Runs at μ ≈ 8–9 needed 10³–10⁴ evaluations.
- The order at which a *single* random S works half the time solves N e^{−W/N} = ln 2. Over the 27 D ≥ 7 cells it
  is 8–43 % below our records (mean 19 %). The gap is largest at small N, where searches are long relative to the
  cost of one evaluation.

**T tries.** With T independent random S, success needs T·e^{−μ} ≳ 1, so μ* ≈ ln T, and

  N_T ≈ Δ g_Δ (Δ−1)^{D−2} / ln(N_T / ln T).

- Annealing does better than independent tries. SIZE_LAW's measured capability rule, μ_max(M) = 13 + 2 ln(M/10⁵)
  for M evaluations (from one cell, (7,8)), corresponds to T_eff ≈ (M/150)² independent samples.
- One evaluation costs ∝ N: a BFS of the whole group, two for odd D (§8 of SIZE_LAW, c ≈ 0.45–1.5 ns per element).
- So a fixed wall-clock budget B buys M = B/(c N b) evaluations, giving μ* = const − 2 ln N + 2 ln B.
- Prediction: slope dμ*/d ln N = −2. Observed: −2.34 ± 0.18 (all D), −2.23 ± 0.20 (D ≥ 7).

**One-parameter test.** Take the capability rule as given, with SIZE_LAW §8's c and b. Fit only B, one budget for
every order, then solve N e^{−W/N}·ε_G = μ_max(M(N)) for each D ≥ 7 cell. Here ε_G is the group's model excess
from THRESHOLD §3, held fixed near its order.

| model | free parameters | rms log error in N (27 cells, D ≥ 7) | LOO rms | mean error D7 / D8 / D9 / D10 |
|---|---|---|---|---|
| budget model, with group excess | 1 (B = 708 s) | **0.020** | 0.020 | +0.032 / −0.007 / −0.007 / −0.003 |
| budget model, generic μ | 1 (B = 596 s) | 0.022 | 0.022 | +0.032 / −0.011 / −0.010 / −0.003 |
| constant μ* | 1 (μ* = 17.4) | 0.049 | | |
| SIZE_LAW ln μ* = a + b ln N | 2 | 0.022 (LOO, 19 cells) | | |

**Verdict.** "Best of T" with T set by a fixed per-order budget accounts for all of the remaining drift.
- The mean residual per D is below 1 % for D = 8, 9, 10.
- The one-parameter model does as well as SIZE_LAW's two-parameter fit.
- The fitted budget (~10 core-minutes per order, at this machine constant) is the right order of magnitude for
  the actual runs (90 s to 1 h each, 1–4 seeds).

**Caveats.**
- Budgets were not really constant.
- The capability rule was calibrated at a single cell.
- The machine constant c jumps at N = 10⁷.
- D = 7 has two cells, and (6,7) is small-N, near-exhaustive search.
- So this is a consistency check, not an independent prediction.
- What it rules out: any need for an extra D-dependent effect beyond ln N and the search budget.

## 4. Special targets and coincidences (THRESHOLD §3) in the data

**(a) Screening order at (6,9), N = 58,752.** This is odd D. HAAR_GEN_NOTES ran random-S screens, no search,
and reported the 10th-percentile cost. The model's mean uncovered count is the generic part plus the
involution/centre terms plus the junction-swap loss. Nothing was fitted.

| group | involutions | model E[uncovered] | observed p10 cost |
|---|---|---|---|
| SL(2,17)×Z₁₂ | 3 | 37.5 | 42 |
| PSL(2,17)×Z₂₄ | 307 | 54.7 | 54 |
| PGL(2,17)×Z₁₂ | 579 | 68.0 | 68 |
| PSL(2,49) | 1,225 | 103 | 83 |

- The ordering is exactly right.
- The size of the PSL/PGL penalty is right. Observed p10 ratios to SL are 1.29, 1.62 and 1.98; the model mean
  ratios are 1.46, 1.81 and 2.75.
- The near-equality of the middle two rows is partly luck, since p10 and mean are different statistics.
- The generic formula gives the same 2μ = 28.9 for all four groups.

**(b) The (7,9) wall.** PSL(2,29)×Z₁₇ stuck at cost 2 at N = 207,060, below the SL(2,31)×Z₇ record of 208,320.
- Generic μ is 12.3 vs 13.1, so PSL looks *easier*.
- Model μ is 21.4 vs 14.1, of which 7.1 comes from the 435 involution targets. That explains the wall.

**(c) Parity × family.**
- Among the 58 even-D files (D ≥ 7), 15 use groups with ≥ √N involutions (pure PSL, PGL, PSL×PSL), and 2 of
  those are cell records.
- Among the 39 odd-D files, only one does: PSL(2,31)×Z₃₈ at (8,9).
  - It is not a record: N = 565,440, μ = 3.9, far below its cell's 12.7.
  - With the involution term, its μ is 9.8.
- No pure PSL or PGL group holds an odd-D record. This matches THRESHOLD Corollary 5.2. Odd D penalises
  involution-rich groups; even D does not.
- (Partly this reflects the searchers' own screening, which learned the same thing empirically.)

**(d) Effect on the records themselves is small.**
- Record groups are SL(2,q) × small Z_m or SL × SL, with 1–3 involutions and |Z| ≤ 48.
- For odd-D records the special-target share is 1–11 % of μ: largest for SL(2,109)×Z₂₄ at (13,9) (11 %) and
  PSL(2,5)×SL(2,25)×Z₄ at (10,9) (9.5 %).
- That is ≤ 1 % in N.
- For even D the model has no structural term.

**(e) What is not explained.** At record scale SIZE_LAW §2.3.2 measured a mean excess
ε = E[uncovered]/μ ≈ 1.3–2.2 for good groups, and ≈ 8 for SL(2,8)×Z₂₁₁. The first-order model gives 1.00–1.13,
and 1.54 for SL(2,8)×Z₂₁₁, where the rearrangement term with |G'| = 504 is all of it.
- So most of the record-scale excess is a fixed-Δ effect not in the model. Likely candidates:
  - heavy-tailed variation across S;
  - short relations among the Δ = 7–9 letters, e.g. s_i^{−1}s_j of small order;
  - repeated-letter words, which are a large share at Δ = 8, ℓ = 7.
- It costs about ln ε/(W/N) ≈ 3–6 % in N and is absorbed in μ*.

## 5. Theorems 1–2 against the data

- **Theorem 1:** W(Δ,D) = Σ_{j<D}(Δ−1)^j, the bipartite Moore bound per side, was checked as an identity for
  Δ = 3..19 and D = 2..11.
  - Every record has N ≤ W, as it must: N/W = 0.053–0.52 over the 117 files.
  - The *log-factor* gap is what the random theory explains: W/N = 1.9–18.9 ≈ ln(N/μ*).
  - Side remark: d ln N = d ln μ*/(1 + W/N), not /(W/N − 1) as SIZE_LAW §4.1 writes. This is a sign slip there,
    about 20 % on its "+3–4 % per 10× compute".
- **Theorem 2:** |G/G'| ≤ A(Δ,D) holds for all 117 records.
  - The tightest are D = 5 metacyclic and nilpotent groups: Z₂₈₈⋊Z₃ (|G^ab| = 288 vs A = 869), Heisenberg(5)×Z₇
    (175 vs 869).
  - A(Δ,D) is tiny next to W. For example A(8,8) = 15,128 vs W = 960,800; A(16,10) = 2.3·10⁷ vs W ≈ 3·10¹⁰.
  - So for D ≥ 8 the cyclic factors (m ≤ 82 in our records) are nowhere near the bound. The bound rules out
    abelian or large-abelianization groups, not our families.

## 6. Monte Carlo in and near the theorem's regime

`sim.py`: n = 1320, 300 trials per point, multiplication tables. `sim2.py`: SL/PSL(2,p) up to n = 68,880,
200 trials per point, direct matrix arithmetic.

For each point the scripts print three predictions:
- e^{−μ_gen};
- e^{−μ}, with the special targets of §3 (odd D);
- e^{−μ}, also with the first-order coincidence losses (junction swaps; rearrangements with |G'|).

Standard errors are binomial, ≈ 0.02–0.035.

**(a) Four groups of the same order 1320, the same Δ and the same W.** The generic theory cannot tell them apart.

| D | Δ | μ_gen | SL(2,11) | PSL(2,11)×Z₂ | SL(2,5)×Z₁₁ | Z₁₃₂₀ |
|---|---|---|---|---|---|---|
| 4 | 21 | 2.24 | 0.16 (pred 0.11) | 0.04 (pred 0.02) | 0.11 (0.10) | |
| 4 | 23 | 0.28 | 0.80 (0.75) | 0.62 (0.56) | 0.68 (0.75) | |
| 5 | 11 | 0.29 | 0.65 (0.66) | 0.02 (0.002) | 0.48 (0.56) | 0.00 |
| 5 | 12 | 0.01 | 0.96 (0.95) | 0.35 (0.31) | 0.89 (0.93) | 0.00 |
| 5 | 13 | 0.00 | 1.00 (0.99) | 0.87 (0.86) | 0.99 (0.98) | 0.11 |
| 6 | 7 | 1.12 | 0.23 (0.32) | 0.06 (0.03) | 0.17 (0.27) | |

(pred = full model e^{−μ}.)
- The full model separates the groups correctly.
- PSL(2,11)×Z₂ is much worse at every D, because 111 of its 1320 elements are involutions. At odd D this works
  through involution targets; at every D it works through junction swaps.
- The abelian Z₁₃₂₀ fails completely at Δ = 12, where the generic theory predicts 0.99. That is Theorem 2 and
  Corollary 5.3: rearrangements coincide.

**(b) Larger n (`sim2.py`).**

| group | n | D | Δ | P_emp | e^{−μ_gen} | full model |
|---|---|---|---|---|---|---|
| SL(2,23) | 12,144 | 5 | 19 / 20 / 21 | 0.24 / 0.84 / 1.00 | 0.28 / 0.86 / 0.99 | 0.25 / 0.82 / 0.96 |
| SL(2,37) | 50,616 | 5 | 27 / 28 / 29 | 0.02 / 0.31 / 0.80 | 0.02 / 0.39 / 0.84 | 0.01 / 0.37 / 0.81 |
| PSL(2,23) | 6,072 | 5 | 16 / 17 | 0.00 / 0.14 | 0.45 / 0.94 | 0.00 / 0.09 |
| PSL(2,37) | 25,308 | 5 | 24 / 25 | 0.005 / 0.145 | 0.79 / 0.97 | 0.003 / 0.13 |
| SL(2,29) | 24,360 | 4 | 63 / 64 / 65 | 0.38 / 0.51 / 0.64 | 0.31 / 0.49 / 0.65 | same |
| PSL(2,29) | 12,180 | 4 | 49 / 50 / 51 | 0.19 / 0.39 / 0.63 | 0.32 / 0.53 / 0.71 | 0.20 / 0.41 / 0.61 |
| SL(2,5)×Z₃₇ | 4,440 | 5 | 15 / 16 | 0.31 / 0.85 | 0.67 / 0.98 | 0.41 / 0.86 |

- SL(2,p) follows e^{−μ} with no correction.
- PSL(2,p) at odd D needs the involution term. It gives 0.09–0.13 where the generic formula gives 0.94–0.97, and
  the empirical value is 0.14–0.17. This is the (4/3)·n ln n obstruction of Corollary 5.2, seen at finite n.
- At even D, PSL needs only the junction-swap loss.
- SL(2,5)×Z₃₇ has a large centre (|Z| = 74) and a small G' (120). The model under-corrects there (0.41 vs 0.31).

**(c) D = 3: convergence.** At n = 1320 the empirical success rate is *higher* than e^{−μ}: 0.67 vs 0.47 at
μ = 0.75. This is a finite-size effect. Effective μ_eff := −ln P_emp at μ ≈ 1.7–1.8, against the size of the
second-order term Δ³/n²:

| n | 1,320 | 4,896 | 12,144 | 29,760 | 68,880 |
|---|---|---|---|---|---|
| μ_eff/μ | 0.48 | 0.62 | 0.75 | 0.80 | 0.80 |
| Δ³/n² | 0.48 | 0.32 | 0.24 | 0.18 | 0.13 |

- ln(μ_eff/μ)/(Δ³/n²) ≈ −1.2 to −1.7 over the range. That is consistent with a correction exp(−c·Δ³/n²).
- A heuristic estimate gives c ≈ 1: hard-core exclusion plus the fixed size of S, which lowers the variance of
  hit counts.
- The correction → 0 as n → ∞, slowly, like (ln n)^{3/2}/√n. This is inside Theorem 3's error terms, but those
  are only asymptotic.

**(d) Small Δ: an extra failure mode.** At D = 6, Δ = 8 (μ ≈ 0.0005), 3–13 % of random S still fail:
3 % for SL(2,11), 12–13 % for PSL(2,11)×Z₂ and SL(2,5)×Z₁₁.
- These are atypical S whose few letters satisfy short relations.
- The Poisson picture does not see them, and in the Δ → ∞ regime of Theorem 3 they disappear.
- They matter only when μ ≪ 1, not at the records (μ ≈ 4–40).

## 7. Summary of the data check

1. The theorem's normalisation W/N = ln N − ln μ fits every record. μ at the records is 4–40, slowly falling with N.
   C_D·ln N is **not** constant: it drifts by exactly ln μ/ln N.
2. "Best of T": with a fixed per-order compute budget and the measured annealing capability rule, one parameter
   reproduces all 27 D ≥ 7 records to 2 % rms with no D-trend. So the drift of μ* (SIZE_LAW §2.2) is the search
   budget.
3. The group-specific predictions are confirmed, though they barely matter for the records' groups:
   - at odd D, involution-rich groups are penalised (screening order, a wall, the absence of PSL/PGL from odd-D
     records, the Monte Carlo);
   - abelian groups fail.
4. Not explained: the record-scale mean excess ε ≈ 1.3–2 for good groups. It is a fixed-Δ effect worth 3–6 % in N.
