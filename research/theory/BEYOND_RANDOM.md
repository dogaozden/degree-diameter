# Beyond random S: why orbit-symmetric generator sets beat the random-S threshold

theory job "cd-theory", second session, 2026-10-23. Builds on `THRESHOLD.md` (the random-S law) and
`DATA_CHECK.md` (budget model), and explains the orbit records of the structured search
(`research/structured/STRUCTURE.md` on branch `claude/structured-haar-search-ws7bet`; solution files
`research/frontier/sols/*orb3*`). Scripts and saved outputs are in `scripts/` (listed in §6).

Notation as in THRESHOLD.md and STRUCTURE.md:
- N = |G|; W = W(Δ,D) is the number of binding words; λ = W/N; μ = N e^{−λ}; ℓ = D − 1.
- α is an automorphism of prime order k with α(S) = S, S = F ∪ O_1 ∪ … ∪ O_m: f fixed generators (e included) and
  m orbits {x, αx, …, α^{k−1}x}. So Δ = f + km.
- Fix = Fix(α). In SL/PSL(2,q) × Z_n with α = (conjugation by an element g of order 3) × (z ↦ rz), Fix is the torus
  C(g) of order ≈ q ± 1 (STRUCTURE §2).

**Status tags** as in THRESHOLD.md: [PROVED], [SKETCH] (one named step missing), [HEURISTIC], [MEASURED].

## Short answer

1. **(a) Mechanism.**
   - Orbit-closed S does **not** cover better. It has the same W words, slightly fewer distinct values, and the
     same or a slightly larger expected number of uncovered elements.
   - What changes is the *shape* of failure. The uncovered set is α-invariant, so misses come in clumps of k.
   - A valid S needs zero misses. Its probability is about e^{−μ_A}, where μ_A is the expected number of clumps:
     roughly μ/3 plus a small fixed-point term, instead of μ.
   - So the gain is in P(valid), not in coverage (§1).
2. **The search sees μ_A exactly as it sees μ.** The 32 solved orbit runs follow the random-S effort law of
   SIZE_LAW, evals ≈ 10⁵·e^{(x−13)/2}, with x = μ_A in place of μ.
   - Fitted: slope 0.45 ± 0.08, against 0.5. Intercept 5.1, against 5.0.
   - No free parameter.
   - Applied to plain μ, the same law is off by a factor e^{7.4} ≈ 1600 (§2).
3. **(b) Gain per cell.**
   - At equal search effort the gain is about ln(N_new/N_old) ≈ [ln 3 + ln(1 − Φ/μ_old)]/(1 + λ), where Φ is
     the fixed-point part of μ_A.
   - Without fixed points this is 14 % at λ ≈ 7 and 6 % at λ ≈ 17.
   - Corrected for the evaluations each run actually used, it predicts the 8 cells where both runs' logs exist to
     **2.3 % rms** (mean −1.5 %, about half a ladder rung).
   - Over all 15 cells the equal-effort prediction is 3 points too high on average. The shortfall is in the big
     cells, which got 9–3,400 evaluations, and in (9,8) (§3).
4. **Two ceilings.**
   - In the small cells, (7,8), (8,7) and (7,9), the orbit records already sit 2–4 units of μ_A below the first-moment
     ceiling of the orbit space: only e^{2–4} valid symmetric S are expected. That is the "wall at μ ≈ 45–50", and
     more compute will not move it much.
   - In the big cells the margin is 16–55 units. There compute is the limit, and the model predicts +5–10 % more
     from the same method at a few core-hours per cell (§3.3, §4.5).
5. **(c) Which symmetries.**
   - **Odd k is required.** An involution β in the symmetry group forces same-length coincidences v = β(v)^{−1}
     on every even-length subword with v ∈ Anti(β).
   - Proved: |Fix(β)|·|Anti(β)| ≥ N. So few fixed points means many collisions.
   - This covers order 2 and order 4, conjugation by normaliser elements of a torus, and the diagonal (PGL)
     automorphisms (§4.2).
   - Among odd k, conjugation of order 3 is right for SL(2,q) × Z_n at moderate size. Order 5 helps at (11,9)
     and (10,10), where λ ≥ 13. It is also the only feasible option for the open cell (11,8).
   - Frobenius of order k has a fixed-point cost that stays bounded for every k. It is the only route to large k.
6. **Why the field automorphism lost** (STRUCTURE §5). On SL(2,8), Fix(Frobenius) = SL(2,2) ≅ S₃: five
   non-identity elements, three of them involutions.
   - The extra fixed generator is drawn from it. If it is an involution t, e·t^{−1} = t·e^{−1} wipes out about 9 %
     of the words.
   - At odd D the fixed involutions are missed at rate e^{−λ/6}.
   - On SL(2,64), where Fix(Frobenius) = SL(2,4) has 60 elements against 63 for conjugation, the two cost
     distributions are identical (§4.3, measured here). The loss was a small-field artefact.

---

## 1. The mechanism: same words, clumped misses

### 1.1 Exact facts [PROVED]

1. α is an automorphism of H(G,S) that fixes (e,A) and (e,B). So the ball of radius ℓ and the uncovered set U are
   α-invariant: U is a union of α-orbits.
2. The letter permutation σ induced by α permutes the binding words, with (σw)(S) = α(w(S)). The number of words
   is still W. A word w and σw take the same value only if that value is α-fixed.
3. **Uncertainty lemma.** Let N_α(u) := u·α(u)⋯α^{k−1}(u). The map L(x) = x^{−1}α(x) satisfies
   N_α(L(x)) = x^{−1}α^k(x) = e (the product telescopes). Also L(x) = L(y) iff yx^{−1} ∈ Fix. Hence

       |{u : N_α(u) = e}| ≥ N / |Fix(α)|.

   For k = 2 the set on the left is Anti(α) := {u : α(u) = u^{−1}}. Few fixed points therefore force many
   "norm-trivial" elements, and those create word coincidences (§1.4).

### 1.2 The clumped Poisson law

Let A = ⟨α⟩, extended by the inversion for odd D (which already pairs x with x^{−1}; THRESHOLD §3). Let Stab(x)
be the stabiliser of x in A. Every word hitting x has |Stab(x)| − 1 images under Stab(x) that also hit x, so the
words hitting x come in groups of |Stab(x)|. That gives miss rate e^{−λ_x/|Stab(x)|} per clump. The expected
number of uncovered clumps is

    μ_A = sides · Σ_x (|Stab(x)|/|A|) · exp(−λ_x/|Stab(x)|).                                      (1)

- For random S (A = 1, or the inversion at odd D) this is exactly the model.py mean of THRESHOLD §3.
- For k = 3 at even D: μ_A = (N − |Fix|)e^{−λ}/3 + (|Fix| − 1)e^{−λ/3}.
- At odd D the classes split further (fixed involutions get rate λ/6, non-fixed involutions λ/2;
  `orbit_model.py`).
- The structured job's estimate, μ_eff = μ/k + |Fix|e^{−λ/k}, is (1) at even D, up to counting e. At odd D it
  double-counts the inverse pairs among the fixed points.

**Claim.** P(S valid) ≈ e^{−μ_A}, for a random α-invariant S.
- [SKETCH] in the D-fixed regime of THRESHOLD Theorems 3–4, with m → ∞ orbits and k, f fixed.
  - Keep only words whose ℓ letters come from ℓ distinct orbits. The others are a fraction O(ℓ²k/Δ).
  - Such a word is exactly uniform.
  - Two such words with different *orbit supports* are exactly independent. This is Lemma 2.1 of THRESHOLD with
    "letter" replaced by "orbit": pick an orbit in T ∖ T′, condition on the rest, and the word becomes
    a·α^i(x_j)^{±1}·b with x_j uniform.
  - Within one orbit support, the k global phase shifts of a word map its value by α. So a free target sees them
    as k different targets, and a fixed target sees them as one word counted k times. All other phase patterns
    coincide only with probability O(1/q). This is the analogue of gap G1, and it is the missing step.
  - Suen and the second moment then go through clump by clump, as in Theorem 4.
- [HEURISTIC] for the records' fixed-Δ regime, as Conjecture 6 is for random S. §2 tests it.

### 1.3 Why a search gains from clumping although the mean does not move

- E|U| is the same μ or slightly more: free elements are missed at rate e^{−λ} as before, and fixed elements more
  often.
- A valid S needs U = ∅. Random S has about μ independent chances to fail. Orbit S has μ/3 independent chances,
  each of which costs three elements at once.
- The variance of |U| goes up by a factor of about k, and P(|U| = 0) = e^{−μ/k} instead of e^{−μ}.
- The question "fewer distinct words but better spread?" therefore has the answer **no on both counts**:
  - there are slightly fewer distinct words (§1.4);
  - the spread is worse in the sense of positive correlation: perfect within a clump, and asymptotically
    independent between clumps.
- The gain comes entirely from concentrating the failures.

### 1.4 Distinct words and coincidences, measured [MEASURED]

`collisions.py` enumerates all reduced binding words up to length 4 or 5. It counts distinct values per S and
classifies every coinciding pair by its letter pattern. All 150–300 samples per row are taken on both sides
(`coll_*.txt`).

| group, Δ, word length | random S: median loss | conj k=3: median (p90) | other |
|---|---|---|---|
| SL(2,37)×Z₁₃, Δ=8, ≤4 | 0.14 % | 0.86 % (4.5 %) | |
| SL(2,27)×Z₁₃, Δ=9 (f=3), ≤4 | 0.98 % | 3.55 % (12 %) | Frobenius 4.1 %, without involution generators 3.3 % |
| PSL(2,19)×Z₁₄, Δ=7, ≤5 | 10.7 % (birthday: 9.1 %) | 16.0 % (30 %) | |
| SL(2,8)×Z₄₃, Δ=8, ≤4 | 7.7 % | 9.4 % (20 %) | Frobenius 15.3 %, without involution generators 12.5 % |
| SL(2,37)×Z₁₃, Δ=7, ≤4 | 0.26 % | 0.64 % (4.6 %) | conj k=2: 1.3 % (15 %), mean 4.0 % |

So symmetric S lose more short words, with a heavy tail of degenerate S. The coinciding patterns fall into four
families.

1. **Norm relations (odd k).** If N_α(u) = e for a short product u of letters, then u^{−1} = α^{k−1}(u)⋯α(u).
   - The classifier's most common k = 3 patterns are exactly this. For example `a0 b0 = b1 a1 b2 a2` is the case
     u = x^{−1}y. Similarly `e a0 e b0 = a1 e a2 b0`.
   - Each relation equates a pattern of length 2j with one of length 2(k − j).
   - For k = 3 the shorter side has 2 letters, so the coincidence costs only words containing a specific
     4-letter pattern. The fraction lost is about ℓ/Δ⁴ per degenerate u.
   - By the uncertainty lemma a given u is degenerate with probability ρ ≥ 1/|Fix|; for conjugation in SL(2,q),
     ρ ≈ 1/(q ± 1).
   - With about Δ² short products, the expected loss is about ℓρ/Δ², a few tenths of a percent. It is
     concentrated on a minority of S, which the annealer avoids. The search data show no penalty growing with
     1/|Fix| (§2).
2. **Abelian fixed letters (f = 3).** Fix = C(g) is abelian. Three fixed letters therefore satisfy
   x y^{−1} z = z y^{−1} x, as in the patterns `e F2 F3 a0 = F3 F2 e a0` at the top of the f = 3 list.
   - About 2–5 % of words carry such a window, so λ drops by that fraction.
   - This is the "Δ ≡ 0 mod 3 is weak" of STRUCTURE §7. The fix is f = 0 (§4.5).
3. **Small-order fixed letters.** If a fixed generator t is an involution, then e·t^{−1} = t·e^{−1}. If t³ = e, then
   e t^{−1} e = t e^{−1} t. Every junction between e and t is a coincidence.
   - This dominates the Frobenius case on SL(2,8): `e F2 a0 b0 = F2 e a0 b0` occurs 11 times per S.
4. **Same-length reflections (k = 2).** See §4.2.

### 1.5 The first-moment ceiling [HEURISTIC]

- There are about #S ≈ (N/k)^m |Fix|^{f−1}/m! symmetric sets.
- Valid symmetric S exist, in expectation, while μ_A < ln #S. With μ_A ≈ μ/k this caps μ at about
  k·m·ln N ≈ (Δ − f) ln N. That is the same ceiling as random S (STRUCTURE §1).
- New here: the *margin* ln #S − μ_A at the current orbit records.

| cell | record group | ln #S | μ_A (generic) | margin |
|---|---|---|---|---|
| (8,7) | SL(2,8)×Z₄₃ | 19.3 | 17.2 | 2.1 |
| (7,8) | PSL(2,19)×Z₁₄ | 18.7 | 16.0 | 2.7 |
| (7,9) | PSL(2,29)×Z₁₉ | 21.8 | 17.9 | 4.0 |
| (8,8) | PSL(2,17)×Z₄₉ | 22.7 | 13.8 | 8.9 |
| (8,9) | SL(2,37)×Z₁₃ | 27.5 | 11.0 | 16.5 |
| (10,9) | SL(2,83)×Z₇ | 40.5 | 10.3 | 30.3 |
| (13,9) | SL(2,101)×Z₃₁ | 61.5 | 6.8 | 54.8 |

- With m = 2 orbits (Δ = 7, 8) the orbit space holds only e^{2–4} valid S at the record orders. The next orders
  up hold about one.
- That is the wall STRUCTURE measured at μ ≈ 45–50. It is a ceiling, not a lack of compute.
- The big cells are nowhere near their ceiling.

## 2. The search-effort law transfers: the annealer sees μ_A [MEASURED]

`beyond_predict.py` §1–2 computes μ, the model μ and μ_A for all 50 orbit runs in the structured job's logs
(`orb_runs.txt`). It then tests SIZE_LAW's random-S effort law, evals ≈ 10⁵ e^{(x−13)/2}.

- **Solved runs, 32 with ≥ 300 evals.** The fit is ln evals = 5.11 + 0.453·μ_A, with slope se 0.08 and residual sd
  1.65. The rule's own values are 5.01 + 0.5·x.
  - With the rule fixed, the mean residual is −0.39 (sd 1.60).
  - Using μ instead of μ_A gives −7.4 (sd 3.7).
  - So **an orbit search with clumped mean μ_A costs what a random-S search with mean μ_A costs.**
  - This also accounts for STRUCTURE's "e^{μ/4.5} instead of e^{μ/2}". On its (7,8) ladder, μ rises from 23 to 43
    while μ_A rises from 8.4 to 16.0: a ratio of 0.39, not 1/3, because |Fix| goes from 8 to 17 along the ladder.
    So e^{μ_A/2} ≈ e^{0.19μ}, against the measured e^{0.226μ}, which is within the scatter. At fixed |Fix| the
    slope would be about 0.17.
- **Unsolved runs, 13.**
  - Three stopped before the rule's typical effort.
  - The other ten ran 2–33 times longer than the typical effort (median 6.4×). That is 0.4–2.1 residual sd: the
    edge of each ladder, as expected.
  - The two runs that are hopeless by the rule are PSL(2,257) and PSL(2,397) at odd D. Their μ_A is 39 and 34,
    from the involution targets: q²/2 involutions with rate λ/2, or λ/6 if fixed. That is THRESHOLD Cor. 5.2,
    carried over.
- **Head-to-head** (`cmp_runs.txt`: same groups and seeds, 60 s each).
  - On PSL(2,17)×Z₁₉, μ = 34: random S is 0/4 at about 1.3·10⁶ evals (rule for μ = 34: 3.6·10⁹). Orbit is 4/4 at
    1.7–5.8·10⁴ evals (rule for μ_A = 12.0: 6.2·10⁴).
  - On PSL(2,19)×Z₁₄, μ = 43: orbit is 1/4 at 2.3·10⁵ (rule for μ_A = 16.0: 4.4·10⁵).
- **Residual outliers.**
  - SL(2,27)×Z₁₃ at (9,8), f = 3: +3.4 in ln evals, the abelian-triple effect of §1.4. A rerun with f = 0 solved
    the same group in 1.5·10⁵ evals, against 5.0·10⁵ (one seed each; `exp/an_98_sl27_f0.log`, §4.5).
  - SL(2,8)×Z₄₃ at (8,7): −4.2, i.e. faster than the rule. The rule is calibrated at N ≈ 45,000 and extrapolates
    poorly to the smallest groups.

## 3. Quantitative prediction of the gain per cell

### 3.1 Closed form

- Write μ_A(N) ≈ μ(N)/k + Φ, where Φ is the fixed-point part (it varies slowly with N).
- By §2, a search with M evaluations reaches μ_A = μ* with μ* = 13 + 2 ln(M/10⁵); per cell, μ* = μ_old + 2 ln(M_new/M_old).
- Use d ln μ / d ln N = 1 + λ. Then

      ln(N_new/N_old) ≈ [ ln k + ln((μ* − Φ)/μ_old) ] / (1 + λ_old).                                  (2)

- **At equal effort** (μ* = μ_old) this is [ln 3 + ln(1 − Φ/μ_old)]/(1 + λ).
  - Pure clumping (Φ = 0) gives 14.3 % at λ = 6.7, 12.8 % at 7.6, 10.3 % at 9.6, 8.3 % at 12.2, 6.8 % at 15.1 and
    6.0 % at 17.3.
- **Why big cells gain less.** The gain falls with D and with Δ for two reasons:
  - the 1/(1 + λ) factor;
  - Φ/μ_old grows, because the old records there sit at μ_old ≈ 5–10 while Φ ≈ 1.5–3.
- **Each tenfold increase in evaluations** adds 4.6 to μ_A, hence 13.8 to μ. A random-S search gets only 4.6.

### 3.2 Check against the records (`beyond_predict.py` §3, `beyond_predict_out.txt`)

- N_old is the best random-S record (frontier/sols, files without `orb`); N_new is the best solved orbit run.
- Gains are ln(N_new/N_old) in %; vertex counts are 2N.
- **P0** = clumping only. **P1** = numeric equal effort with the full model, i.e. μ_A,model(N) = μ_model(N_old)
  using the new group's fixed-point and involution counts.
- **P3** = (2) with each run's evaluation count. M_old comes from the frontier run logs, which exist for 8 cells.

| cell | N_old → N_new (vertices) | μ_old | λ | actual | P0 | P1 | P3 | evals new / old |
|---|---|---|---|---|---|---|---|---|
| (8,7) | 41,040 → 43,344 | 26.7 | 6.7 | +5.5 | +14.3 | +10.9 | – | 1.9e4 / – |
| (7,8) | 88,920 → 95,760 | 26.3 | 7.6 | +7.4 | +12.8 | +12.0 | +9.2 | 2.6e5 / 3.3e6 |
| (8,8) | 225,792 → 239,904 | 23.2 | 8.5 | +6.1 | +11.6 | +11.0 | – | 8.8e4 / – |
| (9,8) | 497,904 → 511,056 | 17.6 | 9.6 | +2.6 | +10.3 | +9.6 | – | 5.0e5 / – |
| (13,8) | 6,408,480 → 6,604,416 | 16.7 | 12.2 | +3.0 | +8.3 | +7.7 | +7.5 | 5.3e4 / 6.2e4 |
| (7,9) | 416,640 → 462,840 | 14.9 | 9.7 | +10.5 | +10.3 | +7.3 | +9.6 | 1.5e6 / 2.6e5 |
| (8,9) | 1,245,312 → 1,316,016 | 14.8 | 10.8 | +5.5 | +9.3 | +8.8 | +6.2 | 2.2e5 / 3.7e5 |
| (10,9) | 7,488,000 → 8,003,856 | 10.6 | 12.9 | +6.7 | +7.9 | +6.9 | +6.0 | 2.5e4 / 1.9e4 |
| (11,9) | 16,369,920 → 16,792,080 | 11.5 | 13.6 | +2.5 | +7.5 | +6.3 | +4.6 | 5.0e3 / 7.7e3 |
| (13,9) | 62,156,160 → 63,872,400 | 10.6 | 15.1 | +2.7 | +6.8 | +6.5 | – | 281 / – |
| (14,9) | 111,482,880 → 116,068,656 | 8.3 | 15.9 | +4.0 | +6.5 | +3.2 | – | 3.4e3 / – |
| (16,9) | 316,679,760 → 324,164,400 | 4.9 | 17.3 | +2.3 | +6.0 | +3.4 | – | 9 / – |
| (7,10) | 2,147,040 → 2,234,400 | 13.8 | 11.3 | +4.0 | +9.0 | +8.3 | +5.4 | 2.3e4 / 2.0e5 |
| (8,10) | 7,349,616 → 7,802,160 | 10.0 | 12.8 | +6.0 | +8.0 | +7.3 | +9.1 | 7.4e4 / 2.3e4 |
| (10,10) | 57,868,272 → 60,141,120 | 8.3 | 15.1 | +3.9 | +6.8 | +6.4 | – | 833 / – |

Notes on the table:
- The (10,10) row uses the structured branch's SL(2,79)×Z₆₁. The master file, PSL(2,389) at 58,863,480, is
  +1.7 % at 385 evals.
- (13,9), (14,9) and (16,9) are on the structured branch only.

**Verdict.**
- P0 overpredicts by 4.2 % on average (rms 4.8 %). P1 overpredicts by 2.9 % (rms 3.9 %, 15 cells).
- **P3, the only one that knows the budgets, is off by −1.5 % mean and 2.3 % rms, with correlation 0.71 (8 cells).**
- The remaining −1.5 % is about half a ladder rung: rungs are 2–3 % apart, and the record is the last *solved* rung.
- Two cells beat P1 because they used more evaluations than the old record:
  - (7,9): 1.5·10⁶ against 2.6·10⁵; P3 gives +9.6 against actual +10.5;
  - (8,10): 7.4·10⁴ against 2.3·10⁴; P3 +9.1 against +6.0.
- Of the 7 cells that fall short of P1 by more than 2.5 points:
  - (9,8) is the f = 3 effect;
  - (7,8), (8,7) and (8,8) are near the orbit-space ceiling (§1.5) or used 10× fewer evaluations than the old
    record;
  - (13,9), (14,9) and (16,9) used 9–3,400 evaluations.

### 3.3 What is left in the method (prediction)

- At the same effort as the old random-S records, the k = 3 method should give the P1 column: +3 to +12 %.
- With a fixed **4 core-hours per cell** (evaluation cost ∝ N, DATA_CHECK §3 machine constant), `symmetry_options.py`
  predicts that k = 3 conjugation reaches the following gains over the current orbit records:

| cell | (11,9) | (13,9) | (14,9) | (16,9) | (8,10) | (10,10) | (8,9) | (13,8) |
|---|---|---|---|---|---|---|---|---|
| gain | +8.7 % | +5.9 % | +5.2 % | +6.4 % | +7.3 % | +6.0 % | +6.9 % | +6.3 % |

  The groups are in `symmetry_options_out.txt`.
- The small cells (7,8), (8,7), (8,8) and (7,9) gain about 0, because of the first-moment ceiling of §1.5.
- These are point predictions with the effort law's scatter: a factor 5 in evaluations, about 2–3 % in N.

## 4. Which symmetries should help most

### 4.1 The rule

Formula (1) plus the effort law turn "which symmetry?" into four numbers per candidate.
1. **The clump size |A|.** The generic term is μ/|A|.
2. **The fixed-point cost.** Σ_{H≠1} #{x : Stab(x) = H}·(|H|/|A|)·e^{−λ/|H|}. It needs |Fix(H)| ≪ e^{λ/|H|}.
3. **Coincidences.** They multiply μ by e^{λδ}, where δ is the fraction of words lost.
4. **The first moment.** It needs μ_A ≤ ln #S, which needs enough free orbits.

### 4.2 Order 2 and 4, normaliser elements, diagonal automorphisms: avoid involutions [PROVED + MEASURED]

**Mechanism.**
- Let β be an involution in A. For any even-length subword v, the subword obtained by reversing v, flipping its
  signs and applying the letter map of β has the same length and sign pattern. Its value is β(v)^{−1}.
- So the two words coincide whenever v ∈ Anti(β).
- By the uncertainty lemma, |Anti(β)| ≥ N/|Fix(β)|.
- A top-level word has about ℓ²/4 even subwords, and each is an essentially fresh random element. The loss is
  therefore self-averaging:

      δ ≈ ρ ℓ²/8,  ρ ≥ 1/|Fix(β)|.

- For odd k the analogous relations change the length (2 against 4 letters for k = 3) and cost only O(Δ^{−4}),
  as in §1.4.

**Where it applies.**
- Conjugation by an element of order 4 in SL(2,q) (an involution in PSL): this covers "normaliser elements" of a
  torus, which invert it.
- Diagonal automorphisms of PSL(2,q) from PGL(2,q).
- Any α of order 4, since α² is an involution.
- All have |Fix| ≈ q, hence ρ ≈ 1/q and δ ≈ ℓ²/(8q). With ℓ = 7–9 and q ≈ 20–80 that is 8–50 % of the words,
  which is fatal.

**Measured.**
- On SL(2,37)×Z₁₃ (Δ = 7, words ≤ 4), conjugation of order 2 loses 4.0 % of the words on average. The formula's
  value for length ≤ 4, 2ρ, is 5.6 %. The median is 1.3 % and p90 is 15 %.
- STRUCTURE §2 found the same coincidences on SL(2,13) at the predicted rate.

**Conclusions.**
- k = 2 becomes harmless only when |Fix(β)| ≫ λℓ²/8, roughly ≥ 500. Even then μ/2 loses to μ/3.
- In the reach table (§4.5), conjugation of order 2 is never the best option.
- Frobenius of order 2 on SL(2,q₀²) has |Fix| = |SL(2,q₀)| ≈ q₀³, so the anti-set is small. But it brings a
  second reflection family: `e a0 a1 b0 = a1 a0 e b0` holds iff x commutes with σ(x), i.e. x lies in a σ-stable
  torus. That happens with probability about 1/q₀².
  - Measured on SL(2,25)×Z₃₁ (words ≤ 4): Frobenius of order 2 loses 1.0 % median and 13 % p90. Conjugation of
    order 3 loses 1.5 % and 4.6 %, conjugation of order 2 2.8 % and 17 %. So it has a good median but a heavy tail,
    and the tail is what the self-averaging longer subwords turn into a typical loss at full length.
- **Z₆ = (Frobenius of order 2) × (conjugation of order 3 by g ∈ SL(2,q₀))** on SL(2,q₀²)×Z_n.
  - The orbits have size 6, and every stabiliser type has a bounded fixed-point cost.
  - But it inherits the σ reflections, at rate about 1/q₀².
  - The model ranks it below plain k = 3 for every cell with q₀ ≤ 17. It is the second-best option only at
    (13,8), (10,10) and (16,9) (§4.5).

### 4.3 Field automorphisms against conjugation [MEASURED]

**Scaling.** In SL(2,q)×Z_n, N ≈ q³n and e^{−λ} = μ/N. Then:
- **Conjugation of order k:** |Fix| ≈ q, so the fixed cost is q(μ/N)^{1/k} = μ^{1/k} q^{1−3/k} n^{−1/k}.
  - It is bounded for k = 3.
  - It grows like q^{2/5} for k = 5 and q^{4/7} for k = 7. That is why k ≥ 5 needs small q (STRUCTURE §2.3).
- **Frobenius of order k on SL(2,p^k):** |Fix| = |SL(2,p)| ≈ q^{3/k}, so the fixed cost is (μ/n)^{1/k}, bounded
  for every k.
  - The price: the field must be p^k, and the fixed set is the small non-abelian group SL(2,p), full of
    low-order elements.

**Why Frobenius lost on SL(2,8)×Z₄₃ at (8,7).**
- Fix = SL(2,2) ≅ S₃. Three of its five non-identity elements are involutions.
- The second fixed generator (f = 2) is drawn from it. When it is an involution t, the junctions e·t^{−1} = t·e^{−1}
  collapse about 9 % of the words.
- At odd D, the 3 fixed involutions are clumps with stabiliser of order 6, missed at rate e^{−λ/6}. That adds +2.1
  to μ_A against 0 for conjugation, whose fixed set is the torus Z₉ of odd order.
- Measured over 1,000 random symmetric S (`exp/lv_87_sl8_43_*`):

| quantity | conjugation | Frobenius | random |
|---|---|---|---|
| min cost | 17 | 37 | 51 |
| p10 | 95 | 150 | 108 |
| median | 255 | 412 | 182 |

- Median word loss at length ≤ 4: 9.4 % for conjugation, 15.3 % for Frobenius.
- So the field automorphism was not intrinsically worse. Its fixed group was too small and full of involutions.

**Test of that explanation.** On SL(2,64)×Z₁₃ at (13,8), Fix(Frobenius x ↦ x⁴) = SL(2,4) has 60 elements and
Fix(conjugation) = C(g) has 63. With f = 1 there are no fixed generators. Over 150 random symmetric S each
(`exp/ro_138_sl64_*`):

| quantity | conjugation | Frobenius | random S |
|---|---|---|---|
| min | 18 | 18 | 26 |
| p10 | 30 | 31 | 32 |
| median | 49 | 51 | 42 |
| mean | 72 | 78 | – |

The two symmetric distributions are identical within noise, as the model predicts. The 40-minute anneals on this
group are reported in §4.5.

### 4.4 Odd D: the involution targets

At odd D a fixed involution has stabiliser ⟨α, inversion⟩ of order 2k, so it is missed at rate e^{−λ/2k}. Fixed
groups that contain involutions are therefore penalised:
- the torus C(g) when q ≡ 1 mod 4 in PSL;
- −I in SL, which is unavoidable but is a single element;
- SL(2,2) for Frobenius on SL(2,8).

THRESHOLD Corollary 5.2 (PSL loses at odd D) carries over unchanged. The non-fixed involutions form clumps of 3
with rate λ/2, so PSL alone at odd D stays hopeless with orbits too. The rule gives μ_A = 39 and 34 for the two
stalled PSL(2,257) and PSL(2,397) runs in the logs.

### 4.5 Concrete, testable suggestions, ranked by expected value

1. **Run the existing k = 3 method longer on the big cells.** This needs no new code.
   - Predicted with 4 core-hours per cell: (11,9) +8.7 %, (8,10) +7.3 %, (8,9) +6.9 %, (16,9) +6.4 %,
     (13,8) +6.3 %, (10,10) +6.0 %, (13,9) +5.9 %, (14,9) +5.2 % over the current orbit records. Also (9,8)
     +10.1 %, with f = 0 (item 2).
   - Groups are in `symmetry_options_out.txt`, "reach" table.
   - Effort rule for planning: evals ≈ 10⁵ e^{(μ_A − 13)/2}, with μ_A from `orbit_model.mu_orbit` (scatter about a
     factor 5).
2. **Δ ≡ 0 mod 3: use f = 0, not f = 3.** That is `ORBIT="3 3 0"` for Δ = 9, `"3 4 0"` for 12, `"3 5 0"` for 15.
   - Three fixed letters in the abelian torus always satisfy x y^{−1} z = z y^{−1} x.
   - Measured at (9,8) on SL(2,27)×Z₁₃, over 400 random symmetric S: f = 0 gives min 7, p10 23, median 56,
     mean 193. f = 3 gives 12, 36, 95 and 4,598.
   - An f = 0 anneal solved the record group in 1.5·10⁵ evals, against 5.0·10⁵ for the f = 3 record run.
   - Not run at all so far: (9,9), (9,10), (12,9), (12,10), (15,8), (15,9). These are the cells STRUCTURE §7 left for
     lack of a good Δ ≡ 0 layout.
3. **Choose fixed generators of large order** in C(g), such as torus generators, never of order 2 or 3. haar_sym
   picks them uniformly from Fix. Restricting the choice is a few lines of code.
4. **k = 5 where μ is large and λ ≥ 13.** The model prefers conjugation of order 5 at:
   - (11,9): +10.3 % on SL(2,61)×Z₄₁, against +8.7 % for k = 3;
   - (10,10): +7.5 % on SL(2,81)×Z₆₁, against +6.0 %.
   - The open cell **(11,8)**: k = 5 on PSL(2,59)×Z₁₁ is the only feasible option. μ_A = 16.7 there, so the rule's
     typical effort is 6.4·10⁵ evals.
   - The two attempts there, at 1.6 and 3.0·10⁶ evals (best 2 and 3, only fixed points left), are 0.6 and 0.9 sd
     beyond that typical effort. That is unlucky but not a contradiction, so more seeds are the recommendation.
   - Every prime of n must be ≡ 1 mod 5.
5. **Frobenius of order 3 at (13,8) on SL(2,64)×Z₁₃** (6,814,080 vertices, above the current 6,604,416): see the
   anneal results below. Conjugation on the same group is equivalent (§4.3).
6. **Do not try k = 2 or 4**, including normaliser and diagonal automorphisms, unless |Fix| ≳ 500. Do not try Z₆
   below q₀ ≈ 17.
7. **Beyond the ceiling.** For Δ = 7, 8 at D = 7–9, every random-like or orbit-symmetric family is close to its
   first-moment ceiling (§1.5). Further gains there need coverings with negative correlation, which is a different
   program (STRUCTURE §7.5).

ANNEAL-RESULTS-PLACEHOLDER

## 5. What is proved, what is not

| statement | status |
|---|---|
| U is α-invariant; words permuted by σ; same W | PROVED |
| Uncertainty lemma \|{N_α = e}\| ≥ N/\|Fix\|; for k = 2, \|Fix\|·\|Anti\| ≥ N | PROVED |
| Formula (1) as the Poisson mean of uncovered clumps | definition; exact first moment of clumps up to the usual coincidence corrections |
| P(valid) → e^{−μ_A}, D fixed, m → ∞ orbits | SKETCH: THRESHOLD Theorems 3–4 with orbit supports; missing step = G1-type bound for phase patterns |
| Same, records' regime | HEURISTIC; tested in §2 |
| Effort law with μ_A in place of μ | MEASURED (32 solved, 13 unsolved runs) |
| Gain formula (2) and the P3 check | HEURISTIC + MEASURED (rms 2.3 %, 8 cells) |
| k = 2 loss δ ≈ ρℓ²/8 | first-order HEURISTIC, MEASURED order of magnitude |
| Odd-k norm coincidences cost O(ℓρ/Δ²) | first-order HEURISTIC, consistent with the measured short-word losses |
| f = 3 abelian triples, low-order fixed letters | exact identities; size MEASURED |

## 6. Files (all in `scripts/`; run from that folder)

- `orbit_model.py`: formula (1) for α-invariant S, with the fixed-point structure of conjugation of order 3 on
  SL/PSL/PGL(2,q) × Z_n. It matches haar_sym's |Fix| on all 50 runs.
- `beyond_predict.py` → `beyond_predict_out.txt`: §1–3 (every run's μ and μ_A, the effort law, gain predictions
  P0, P1 and P3).
  - Data: `orb_runs.txt` (RESULT lines of the structured job's logs at commit c8e7452) and `cmp_runs.txt`
    (its head-to-head). Old evals are read from `../../frontier/{runs,wave3,wave4}`.
- `symgroups.py`, `collisions.py` → `coll_*.txt`: exact word enumeration and the coincidence classifier (§1.4,
  §4.2). Usage is in the file header.
- `symmetry_options.py` → `symmetry_options_out.txt`: §4.5, μ_A for each candidate symmetry and group, and the
  reach table.
- `exp/`: the haar_sym screening and anneal runs of this session (§4.3, §4.5).
  - Built from `research/structured/haar_sym.c` of the structured branch, unchanged.
  - Commands are at the top of `exp/README.md`.
