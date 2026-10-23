# Summary for Doğa: does the size law become a theorem?

**One sentence.** Yes, but only in one regime. In the regime where we can prove things (D fixed, many generators),
a random Haar graph of essentially any well-mixing group has diameter ≤ D once the word count W passes n·ln n. That
coupon-collector log is exactly the factor that makes C_D drift down with D. In the regime of our records (Δ fixed,
D growing), the same statement is a well-supported conjecture that nobody can currently prove.

## What is proved (THRESHOLD.md)

1. **Counting bound, any S.** |G| ≤ W(Δ,D), and this equals the bipartite Moore bound per side exactly. No log
   factor is possible for arbitrary S: Singer difference sets reach n = W at D = 3.
2. **Abelian bound.** The abelian part of G can have at most A(Δ,D) = O(D^{Δ−1}) elements. Abelian groups are
   therefore useless at large D, and the randomness must come from the commutator subgroup.
3. **The main theorem, for every finite group (D fixed, Δ large).** The probability that a given element x is not
   reached is exp(−C(Δ, D−1)·β(x)), up to a vanishing error.
   - β(x) is a single explicit number: the chance that D−1 random group elements, in some order with alternating
     signs, multiply to x.
   - From this, a sharp 0/1 law follows: diameter ≤ D whp when Σ_x e^{−C·β(x)} → 0, and > D whp when it is
     ≫ log n.
   - Consequence: for **every** group the threshold is between n ln n and (D−1)!·n ln n words.
   - Below n(ln n − ln ln n) words, the diameter exceeds D whp. That is part (c) of the brief, and slightly better.
4. **The group matters, in a computable way.**
   - Every element x with β(x) below the generic value ℓ!/n (ℓ = D − 1) hurts.
   - For PSL(2,q) and PGL(2,q) at odd D, the ~n^{2/3} involutions push the threshold to at least (4/3)·n ln n.
     This is proved.
   - For SL(2,q), with one involution, the lower half (diameter > D below n ln n) is proved. The upper half (≤ D
     above n ln n) is proved except for one algebraic-geometry step, gap G1: a fiber-dimension statement for
     pairs of words in SL₂.

## What is not proved

- **The records' regime** (fixed Δ = 5–16, D = 5–10) is Conjecture 6: diam = log_{Δ−1} n + log_{Δ−1} ln n + O(1)
  for random S in SL(2,q).
- The best rigorous result is diameter ≤ C·log n from Bourgain–Gamburd, with C unknown and large.
- The obstruction is precise (gap G2). With only Δ random letters, the K-wise independence the standard methods
  need is impossible for K > Δ, because there are only n^Δ choices of S.

## How it explains our data (DATA_CHECK.md)

- **The invariant** is W/N = ln N − ln μ*, where μ* is the expected number of misses the search can absorb.
  - C_D·ln N is *not* constant: it falls from 2.3 to 1.17 (in units of Δg) from D = 5 to 10. That drift is exactly
    ln μ*/ln N.
- **"Best of T tries" accounts for the rest.**
  - One random S works with probability about e^{−μ}.
  - Annealing with M evaluations reaches μ* ≈ 2 ln(M/150).
  - Each evaluation costs ∝ N, so a fixed budget makes μ* fall like −2 ln N. Observed: −2.3 ± 0.2.
  - One fitted budget, about 10 core-minutes per order, reproduces all 27 records at D ≥ 7 to 2 % rms, with no
    leftover D-trend.
- **The group effects are real.** These have not been recorded before:
  - At odd D, involution-rich groups (PSL, PGL) lose. The model predicts the recorded screening order at (6,9),
    which is SL < PSL < PGL < PSL(2,49), and the size of the gaps.
  - It explains the PSL(2,29)×Z₁₇ wall at (7,9).
  - No pure PSL or PGL group holds an odd-D record.
  - The Monte Carlo at n up to 69,000 matches e^{−μ} for SL(2,p). For PSL(2,p) at D = 5 the generic formula
    predicts success 0.95; the observed rate is 0.14, and the corrected model gives 0.1.
- **Not explained:** a residual 1.3–2× excess of misses for the good groups at record scale. It is a fixed-Δ
  effect, worth 3–6 % in N.

## Is this a paper?

- **Theory alone:** a solid short paper ("Diameter thresholds for random Haar graphs"), if it is new.
  - The nearest work is Christofides–Markström–Savvidou, arXiv:2605.29457, May 2026. It proves the analogous
    D-fixed thresholds for random *Cayley* graphs, with a window of the same shape.
  - Read it before claiming novelty: it may already contain the method.
  - What we add: the bipartite/alternating-word setting, the per-target law for every group, the odd-D
    involution/centre effects, and the abelian bound.
  - Closing gap G1 would add a clean sharp threshold for SL(2,q). G1 is probably a few pages of algebraic
    geometry, but that is a guess.
- **Theory plus our computations:** a good paper. That means the records, the size law with its budget
  explanation, and the group-effect predictions confirmed in the data.
- **The fixed-Δ conjecture:** would be a major result, but I see no route to it now.

**Caveats.** The literature check was done by web search this session; anything marked [B] or [M] in
LITERATURE.md was not read in full. The Bollobás–Fernandez de la Vega constant in particular needs checking against
the original. Lemma 2.2 uses Yadin's published form of Suen's inequality, not Janson's.

## Second session: beyond random S (BEYOND_RANDOM.md)

- **Why the orbit search wins.** Orbit-symmetric S (order-3 automorphism) do not cover better: they have the same
  words, slightly fewer distinct values and the same mean number of misses. But the misses come in clumps of 3, so
  P(valid) ≈ e^{−μ_A} with μ_A ≈ μ/3 + a small fixed-point term.
- **The search sees μ_A exactly as it sees μ.** The random-S effort law fits the orbit runs with no free
  parameter.
- **Gain per cell.** The gain is ≈ [ln 3 + ln(1 − Φ/μ)]/(1+λ) at equal effort. Corrected for budgets, it predicts
  the records to 2.3 % rms.
- **Two ceilings.** The small cells are at the orbit space's first-moment ceiling. The big cells have +5–10 % left
  for more compute.
- **Avoid involutions in the symmetry group.** Proved: |Fix|·|Anti| ≥ N, so there are same-length coincidences.
- **Frobenius lost only because Fix = SL(2,2) on SL(2,8).** On SL(2,64) it equals conjugation.
- **Concrete suggestions** are ranked in §4.5 (f = 0 for Δ ≡ 0 mod 3, k = 5 at (11,9), (10,10) and (11,8), longer
  runs on big cells).
