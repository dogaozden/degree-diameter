# ORDER2: why an order-2 symmetry won at (6,8), and where even orders win

Job "thm-order2", two Opus cloud sessions (4 cores each): 2026-10-24 (branch `claude/thm-order2-symmetry-gap-4e2nmi`,
cut off by the usage limit) and 2026-10-25 (branch `claude/thm-order2-symmetry-wejgw7`, which carries both).
Scripts, logs and saved outputs are in `order2/` (list in §7). Builds on `research/theory/BEYOND_RANDOM.md`
(branch `claude/cd-theory-beyond-random-3ybyf2`) and on the table-squad log (`research/squads/LOG.md`, branch
`claude/degree-diameter-table-squad-0xgp3g`). The second session added §2.7–2.8, §3.4–3.5, §5.5 and revised the
short answer, §4 and §6; where it overturns a claim of the first session, the old text says so.

Notation as in BEYOND_RANDOM: G of order N, S of size Δ, H(G,S) with edges (g,A) ~ (sg,B), ℓ = D − 1, W the number
of binding words, λ = W/N, μ = N e^{−λ} (haar_sym's μ). α is an automorphism with α(S) = S, k its order, μ_A the
clumped Poisson mean (BEYOND_RANDOM formula (1)). For an involution β: σ is the letter permutation it induces on S,
ι is inversion, β* = ι∘β (an anti-automorphism), Anti(β) = Fix(β*) = {u : β(u) = u⁻¹}, and ρ = |Anti(β)|/N.
"Evaluations" are haar_sym cost evaluations, the unit of the effort law evals ≈ 10⁵·e^{(μ_A − 13)/2}.

## Short answer

1. **Why order 2 beat order 3 at (6,8): order 3 runs out of sets.** Valid symmetric sets come in classes of
   equivalent Haar graphs (S ↦ a·ψ(S)^{±1}·b, §2.7). On SL(2,25) at (6,8) the order-3 space (two orbits of 3) has
   only **8,773 classes**. 10⁶ uniform samples hit every class about 114 times, so the census is complete: the best
   class has cost 2 and no class has cost 0 (§3.4). Per set, order 3 is the *better* symmetry (fewer uncovered clumps,
   as the rule says), but there are too few sets. The order-2 spaces (three orbits of 2) are much larger:
   2.68·10⁶ classes for the Frobenius involution, of which exactly one is a solution, and 3.42·10⁷ for the
   conjugation involution, of which about 40–60 are (17 valid sets in 10⁷ uniform samples, 14 distinct classes).
   This makes the first session's point 3 exact. The twisted cycles (point 3 below) explain why order 2 is not ruined
   by its involution. They do not explain why it beats order 3.
2. **The gap in BEYOND_RANDOM is "self-averaging".** BEYOND_RANDOM §4.2 computed the mean word loss of an involution,
   δ ≈ ρℓ²/8 with ρ ≥ 1/|Fix(β)|. For both (6,8) winners (ρ ≈ 1/24, ℓ = 7) that is about 25 % of the binding words,
   which would be fatal. The mean is right. What fails is the next step: "each even subword is an essentially fresh
   random element, so the loss is self-averaging". Each coincidence is one *twisted cycle* v·σ(v) of the graph, and
   the same cycle acts at every position of every word. So the loss sits in a few Poisson-distributed cycles,
   and a solution simply avoids the short ones:
   - twisted 4-cycles: mean 0.16–0.5 per random symmetric S at (6,8); none in any solution found;
   - twisted 8-cycles: mean about 4.2; the 17 uniformly sampled conjugation solutions have 0.76 on average (eight
     have none), as the n* law of §3.1 predicts (0.46);
   - twisted 12-cycles: mean 65–80, each nearly free (0.06 % of the words).

   BEYOND_RANDOM's estimate gives P(valid) ≈ e^{−72} for conjugation on SL(2,25); the measured value is e^{−13.3}.
3. **What the twisted cycles cost, measured (second session).** The first session's rule charges a symmetry
   Σ_j R_j(1 − e^{−x_j}) nats for its twisted cycles and read the four-way test at (6,8) as confirming it. Counting
   solutions in 10⁷ uniform samples per symmetry (§3.4) gives a sharper picture.
   - **Short cycles: paid, as avoidance.** On PSL(2,11)×Z24, doubling the twisted-cycle density (r = 23 instead of
     11) empties the lower tail: no set below cost 9, against 2 solutions and 450 sets of cost ≤ 8.
   - **Long cycles and the absolute level: not as charged.** One formula fits all four order-2 spaces to within
     0.4 nats: P(valid) ≈ P(no twisted 4- or 8-cycle)·e^{−(μ_A⁰ − 6)}. The charged rule is 7–10 nats too
     pessimistic.
   - **It gets one comparison backwards.** On SL(2,25), conjugation has 4.6 times the solution density of Frobenius
     (≈ 50 classes against 1), although the annealer found the Frobenius class more often (5/6 seeds against 2/6,
     Fisher p = 0.12).
4. **Even D matters for order 2, and odd D allows order 6 (second session).** At odd D each side's word set is
   inverse-closed, so β* = ι∘β is a symmetry and every element of Anti(β) is a target whose words come in pairs:
   missed at rate √p instead of p. The first session concluded that even orders are excluded at odd D. That holds for
   k = 2 (order 3 always wins) and for conjugation-type involutions, but not in general. **σ-palindromic words always
   land in Anti(β)**, on the image of the Lang map u ↦ β(u)⁻¹u (§2.8). For a tight, balanced involution
   (|Fix(β)| = |Anti(β)| = √N) each Anti element gets about √λ extra shots, so it is missed at e^{−λ/2−√λ} rather
   than e^{−λ/2}, and the Anti penalty nearly vanishes (§3.5). Measured at (12,7): Anti elements of the Frobenius
   involution on SL(2,64) are missed only 1.7× as often as generic ones (predicted 1.9; without palindromes 41).
   The formula also explains the first session's unexplained (6,9) numbers. Consequence: **at odd D an order-6
   symmetry whose involution is tight and balanced has about half the uncovered clumps of order 3.** Three screens:
   SL(2,64) and SL(2,8)² at (12,7), PSL(2,25)² at (14,9) (§5.5).
5. **The fixed points are not the issue** at D = 8: 24 fixed points cost 24·e^{−λ/2} ≈ 1.1 missed elements.
6. **Corrected rule** (§4). Count uncovered clumps, μ_A = μ/k + Σ_H (fixed points of H at e^{−λ/|H|}) + [odd D]
   (Anti elements of each involution at e^{−λ/2−π}, π = palindromic shots); prefer the symmetry with the smallest μ_A,
   **provided its orbit space has enough classes**. Roughly, ln(#classes) must exceed μ_A by a margin.
   Short twisted cycles (μ_A⁰λc_j ≳ 1) are paid as avoidance, −ln P(none); long ones are free. The absolute
   P(valid) = e^{−μ_A} was about 6 nats too pessimistic at (6,8), so at small N measure the space directly: 10⁷
   samples cost 4–13 minutes.
7. **Prediction tested: even orders win at even D when every involution in ⟨α⟩ has a large centralizer.** Order 6
   (the Frobenius x ↦ x² of GF(64), whose cube x ↦ x⁸ is an involution fixing SL(2,8)) on the (13,8) record group
   SL(2,64)×Z13:
   - 3 of 3 seeds solved, in 4,665, 9,625 and 37,185 evaluations;
   - order 3 needed 170,313 evaluations (one seed, BEYOND_RANDOM);
   - the rule predicted ≈ 10⁴ and 1.1·10⁵ (§5.1).

   **Record Δ13·D8 = 6,999,552 vertices** (first session; was 6,814,080, +2.7 %; harvested and cloud-checked by the
   coordinator). Order 6 on SL(2,7)²×Z31, with α(x₁, x₂, z) = (c x₂ c⁻¹, x₁, 6z) and c of order 3, ORBIT="6 2 1".
   Four independent checks passed (§5.2).
8. **Where else:** order 2 only where order 3 is starved, i.e. Δ = 6 at small N; in the current table that is
   (6,8) alone (§5.3). Order 6 at even D: (13,8) (done), (15,8) with orbits 6+6+3, (13,10) on SL(2,16)²×Z21.
   Order 6 at odd D (new): Δ ≥ 12 with a tight balanced involution, best candidate (15,9) on SL(2,64)×Z403,
   +1.5 % (§5.5). Results of this session's runs: RESULTS-SUMMARY.

---

## 1. The puzzle

BEYOND_RANDOM §4.2 ("Order 2 and 4 … avoid involutions") predicted that any involutive symmetry loses
δ ≈ ρℓ²/8 of the binding words, with ρ ≥ 1/|Fix(β)|, and that this multiplies μ by e^{λδ}. For conjugation by a
trace-0 matrix in SL(2,q) it estimated 8–50 % of the words lost and concluded "do not try k = 2 or 4 unless |Fix| ≳ 500".

Then the table-squad Opus solved (6,8) with ORBIT="2 3 0" (three orbits of size 2):

| group | N | α | \|Fix\| | ρ | μ | predicted loss ρℓ²/8 | result |
|---|---|---|---|---|---|---|---|
| SL(2,25) | 15,600 | conjugation by a trace-0 matrix | 24 | 1/24.0 | 29.8 | 25 % (×4.9 on μ) | solved, 2.06·10⁶ evals |
| PSL(2,11)×Z24 | 15,840 | conjugation by an involution, z ↦ 11z | 24 | 1/23.6 | 33.3 | 26 % (×5.0 on μ) | solved, 3.3·10⁵ evals |

Both are exactly the case the old rule called fatal. By the effort law, a ×5 factor on μ_A ≈ 17 would need about 10¹⁹
evaluations; both solved in about 10⁶.

## 2. What is proved

**2.1 Reflection lemma [PROVED].** Let β be an involutive automorphism with β(S) = S, and let v be an alternating
subword of even length 2j. Reverse v, flip its signs and apply σ. The result v* has the same length and sign pattern
(BEYOND_RANDOM §4.2), and its value is β(v)⁻¹. So v and v* have the same value iff v ∈ Anti(β). Equivalently, the
walk v followed by σ(v) is closed: v·β(v) = e. A coincidence with v* ≠ v as words is therefore one cycle of length 4j
in H(G,S), which we call a *twisted cycle*. It acts at every position of every binding word where its half-words fit.
*Proof:* (σ(rf(v)))(S) = β(v(S)⁻¹), and β(v)⁻¹ = v iff β(v) = v⁻¹. ∎
(Half-words: a twisted cycle of length 4j yields 8j half-words v ∈ Anti, from 4j starting points and 2 directions.)

**2.2 Uncertainty and when it is tight [PROVED].** |Fix(β)|·|Anti(β)| ≥ N (BEYOND_RANDOM §1.1). Equality holds iff
every u ∈ Anti(β) has the form x⁻¹β(x). The cases that occur here:
- Conjugation by a trace-0 matrix of SL(2,q), q odd:
  - |Fix| = |C(g)| = q − 1 and |Anti| = q² + q if q ≡ 1 mod 4;
  - |Fix| = q + 1 and |Anti| = q² − q if q ≡ 3 mod 4.
  - Tight: the product is |SL(2,q)|. (Anti = g⁻¹·{trace-0 matrices}, and the trace-0 count is elementary.)
- Frobenius of order 2 on SL(2,q₀²): |Fix| = |SL(2,q₀)| = q₀(q₀² − 1) and |Anti| = q₀(q₀² + 1). Tight, by
  Lang–Steinberg (x ↦ x⁻¹F(x) is onto the u with uF(u) = 1).
- z ↦ rz on Z_n, r² ≡ 1: |Fix| = gcd(r − 1, n) and |Anti| = gcd(r + 1, n).
  - Tight iff the product is n.
  - z ↦ −z on Z_n with n even is not tight (2n).
  - For n = 24, r = 11 is tight and halves Anti compared with r = 23 = −1. haar_sym's "fewest fixed points, smallest r"
    happened to pick r = 11.
- PSL(2,q), q ≡ 3 mod 4: |Fix| = q + 1 and |Anti| = 1 + q(q−1)/2. Slightly above N/|Fix|.

All of these counts were checked by enumeration (`order2/out/rj/*.log`, `out/ro_*.log`, `out/targets/*.json`).

**2.3 Parity [PROVED].**
- At odd D, ℓ is even. Reversing and flipping a whole A-word of length ℓ gives an A-word, with the value inverted.
  So each side's multiset of word values is invariant under ι, under σ, and hence under β*. Every x ∈ Anti(β) is a
  fixed point of β*.
- At even D, ℓ is odd. Reversing and flipping maps A-words to B-words, so β* is not a symmetry of the binding set.

**2.4 AM–GM [PROVED].** |Fix(β)| + |Anti(β)| ≥ 2√N, with equality iff both are √N. Conjugation-type involutions
of SL(2,q)×Z_n are far from balanced (|Fix| ≈ q, |Anti| ≈ q²). Frobenius of order 2 on SL(2,q₀²) is balanced.

**2.5 Clumps [PROVED, BEYOND_RANDOM].** For any α of order k, the uncovered set is ⟨α⟩-invariant.

**2.6 Expected twisted-cycle counts [PROVED, up to the words without a singleton orbit].**
- Setup: S = {x₁, βx₁, …, x_m, βx_m}, with the x_i independent and uniform on G \ Fix(β) (conditioned on
  distinctness). Let v be a reduced alternating word in which some orbit i occurs exactly once (as x_i or βx_i).
- Conditioning on the other x's, v(S) = a·y^{±1}·b with y uniform on G \ Fix(β). Hence
  P(v(S) ∈ Anti(β)) = |a⁻¹Anti(β)b⁻¹ \ Fix(β)| / (N − |Fix(β)|), which lies between
  (|Anti| − |Fix|)/(N − |Fix|) and |Anti|/(N − |Fix|). That is ρ(1 + O(|Fix|/|Anti| + |Fix|/N)).
- So the expected number of twisted half-words of length 2j is ρ times the number of such words, plus the
  contribution of words in which every orbit occurs at least twice. The σ-palindromes among those are excluded; the
  rest are a fraction that vanishes as m → ∞ for fixed j.
- Dividing by 8j gives R_j = ρΔ(Δ−1)^{2j−1}/(4j).
- At (6,8) (m = 3) the measured counts are ρ × words exactly at length 2 on SL(2,25) (2.00 against 2.00), and
  5–18 % higher at lengths 4 and 6 (§3.1), where words without a singleton orbit are common.
- What is *not* proved is that the counts are Poisson. They are overdispersed, because cycles come in ⟨α⟩-orbits.

**2.7 Classes [PROVED].** For a ∈ G, b ∈ G and ψ ∈ Aut(G), the maps T(x) = a·ψ(x)·b and T(x) = a·ψ(x)⁻¹·b
give isomorphic Haar graphs: H(G, T(S)) ≅ H(G, S). (Left and right translations relabel one side, ψ relabels both,
and S ↦ S⁻¹ swaps the sides.) If S is ⟨α⟩-invariant, then T(S) is ⟨α⟩-invariant for every T that normalises
⟨α⟩ in this group E of maps, and only for those once Stab_E(S) = ⟨α⟩. So the valid sets of the symmetric search space
come in whole **classes** of size |N_E(⟨α⟩)| / |Stab(S)|. If one solution exists, then
P(random symmetric S is valid) ≥ (class size)/(number of symmetric S).
- For SL(2,q) the maps with a, b ∈ Fix(α) and ψ normalising ⟨α⟩ already give the whole class. A Lang–Steinberg count
  for the Frobenius involution, and a direct count for conjugation, give the class sizes at (6,8) on SL(2,25):
  28,800 sets (Frobenius x ↦ x⁵, |Fix| = 120), 2,304 (conjugation by a trace-0 matrix, |Fix| = 24) and 1,536
  (conjugation of order 3; here N_E(⟨α⟩) also contains the maps that invert α).
- Checks: `order2/classsize68.py` enumerates the classes by brute force (`out/classes68/classsize_bruteforce.txt`). The
  order-3 value 1,536 also matches the sampling frequency (114 expected hits per class in 10⁶ samples, 101–138
  observed, §3.4). `symmetry68.py` finds |Stab(S)| = 2 (identity and β) for every (6,8) solution, so none is
  secretly more symmetric.

**2.8 Palindromes land on the Lang image [PROVED].** Let β be an involution with β(S) = S, inducing σ on the letters,
and let w be a σ-palindromic A-word of even length 2m: its letters satisfy s_{2m+1−i} = σ(s_i). Then
w(S) = β(v)⁻¹·v, where v = s_m^{∓} ⋯ s_1 is the right half of w. So w(S) lies in the image of the Lang map
L(x) = β(x)⁻¹x. L is constant exactly on the cosets Fix(β)·x, so |Im L| = N/|Fix(β)|, and Im L ⊆ Anti(β), with
equality iff the bound |Fix|·|Anti| ≥ N of 2.2 is tight.
- *Proof:* the left half of w is β applied to the right half, reversed and inverted, which is β(v)⁻¹. Then
  β(β(v)⁻¹v) = v⁻¹β(v) = (β(v)⁻¹v)⁻¹, so w(S) ∈ Anti(β). And L(x) = L(y) ⟺ yx⁻¹ ∈ Fix(β). ∎
- With f = 0 there are P_ℓ = Σ_{j=1}^{ℓ/2} Δ(Δ−1)^{j−1} such words of length ≤ ℓ. If their half-words are spread over G,
  each element of Im L receives about π = P_ℓ·|Fix(β)|/N of them. These are single shots: a palindrome is its own
  β*-image. For a tight, balanced involution (|Fix| = |Anti| = √N) this gives π ≈ √(λΔ/(Δ−1)), because
  P_ℓ² ≈ W·Δ/(Δ−1).
- This only matters at odd D, where the A-words of length ℓ = D − 1 have even length and β* acts on them (2.3).

## 3. Where the old argument fails (measured)

### 3.1 The word loss is a few Poisson cycles, not a self-averaging fraction

`order2/twist.py` enumerates every reduced even alternating word up to length 6 for each S. It counts the
non-palindromic ones that lie in Anti(β) (twisted) or that equal their own inverse (involutive, the baseline every S
has). It also computes the exact cost and the BFS ball sizes. 4,000 random symmetric S per group,
`out/analyze_6_8.txt`:

| group (α) | generating S | twisted 4-cycles: mean, P(none) | twisted 8-cycles: mean, P(none) | twisted 12-cycles: mean (sd) | P(no 4- and no 8-cycle) |
|---|---|---|---|---|---|
| PSL(2,11)×Z24 (r = 11) | 2,742 | 0.16, 0.85 | 4.3, 0.04 | 78 (26) | 3.9 % |
| PSL(2,11)×Z24 (r = 23) | 2,774 | 0.48, 0.60 | 8.2, 0.003 | 144 (32) | 0.3 % |
| SL(2,25) | 3,987 | 0.25, 0.77 | 4.2, 0.035 | 72 (21) | 3.5 % |

Median cost by class, on SL(2,25) (the PSL group behaves the same; full tables in `out/analyze_6_8.txt`):

| twisted 4-cycles | twisted 8-cycles | samples | min | p10 | median |
|---|---|---|---|---|---|
| 0 | 0 | 138 | 15 | 32 | 62 |
| 0 | 2 | 678 | 8 | 34 | 80 |
| 0 | 4 | 564 | 12 | 51 | 114 |
| 0 | 6 | 183 | 34 | 79 | 222 |
| 0 | 8 | 52 | 82 | 170 | 626 |
| 1 | 4 | 71 | 179 | 234 | 389 |
| 1 | 6 | 181 | 161 | 294 | 483 |

- A least-squares fit ln(cost) ~ n₄ + n₈ + n₁₂ gives per 8-cycle 0.097 (SL(2,25)), 0.156 and 0.104 (PSL r = 11,
  r = 23).
- The first-order prediction is λ·c₂ = 6.2 × 0.021 = 0.13: a twisted 8-cycle removes c₂ = 2·2·4/(6·5³) of the
  words.
- One twisted 4-cycle multiplies the median by 2–4. The first-order prediction is e^{λc₁} with c₁ = 0.4; it
  overshoots, because 40 % of the words is far outside the first-order range.
- The per-12-cycle coefficients (0.004–0.024) are noisy, because n₁₂ hardly varies.

The **two record S** (`twist.py sol`, `out/` and below) have levels 6, 31, 156, 781 at BFS depth 1–4. That is the
maximum: no coincidence at all up to length 4. They have zero twisted 4- and 8-cycles and 56 twisted 12-cycles each,
against means of 78 and 72. Under independence, two draws from a 4 % class have probability 0.0015.

**How many twisted cycles a solution keeps: a parameter-free check.** Let n be the number of twisted cycles of
length 4j. It is Poisson(R_j) over random symmetric S, and each cycle multiplies the clump mean μ_A⁰ by e^{λc_j}.
Summing over n with weight P(valid | n) ≈ exp(−μ_A⁰ e^{λc_j n}) puts the typical solution at

    n* = R_j · exp(−μ_A⁰ λ c_j)

and charges R_j (1 − e^{−μ_A⁰ λ c_j}) nats. This is the Poisson generating function: expensive cycles are paid as
"avoid them all", at R_j nats, and cheap ones as their mean effect. The prediction against every solution in hand
(`out/nstar_table.txt`):

| solution | 4-cycles n* / observed | 8-cycles n* / observed | 12-cycles n* / observed |
|---|---|---|---|
| (6,8) PSL(2,11)×Z24 record | 0.00 / 0 | 0.39 / 0 | 62 / 56 |
| (6,8) SL(2,25) record | 0.00 / 0 | 0.46 / 0 | 61 / 56 |
| (13,8) SL(2,64)×Z13, order 6, three seeds | 0.00 / 0, 0, 0 | 5.2 / 6, 12, 6 | 535 / 563, 605, 578 |
| (13,8) SL(2,7)²×Z31 record, order 6 | 0.00 / 0 | 7.7 / 9 | 802 / 665 |

At Δ = 6 an 8-cycle is expensive (μ_A⁰λc₂ ≈ 2.2), so solutions keep about e^{−2.2} ≈ 1/9 of the random rate. At
Δ = 13 it is nearly free (0.07), so solutions keep the random rate. Twisted cycles come in ⟨α⟩-orbits, which
overdisperses the counts (12 = two orbits of 6).

**Second session: the n* law on an unbiased sample.** The solutions above were found by annealing, which could
prefer some sets. Sampling 10⁷ uniform conjugation-symmetric sets on SL(2,25) at (6,8) gives 17 solutions in 14
distinct classes (§3.4; census `out/classes68/sl25_conj_randorb_census.txt`):
- twisted 4-cycles: none in any of the 17;
- twisted 8-cycles: eight solutions have 0, five have 1, four have 2. The mean is 0.76, against 4.2 for random
  symmetric sets and n* = 0.46;
- twisted 12-cycles: mean 53, against 72 for random sets and n* = 61.

So solutions avoid twisted cycles, as the n* law says. What fails is the step from there to an additive charge on
the number of solutions (§3.4).

**Why the mean misleads.** The mean loss is Σ_j R_j c_j = (ρ/2) Σ_j (ℓ − 2j + 1), which is BEYOND_RANDOM's ρℓ²/8.
The weights ℓ − 2j + 1 = 6, 4, 2 put half of it on 4-cycles and a third on 8-cycles. Those terms are a product of a
rare event (R_j small) and a large effect (c_j large). The "fresh random subword" picture counts the same cycle once
per position and per word, as if each were an independent event.

**Rates.** The twisted half-word counts match ρ × (number of words) on seven groups SL(2,13) … SL(2,31) (300
samples each, `out/rj/`):

| group | ρ | length 2 measured / predicted | length 4 | length 6 |
|---|---|---|---|---|
| SL(2,13) | 1/12 | 3.7 / 5.0 | 130 / 125 | 3,425 / 3,125 |
| SL(2,19) | 1/20 | 2.0 / 3.0 | 72 / 75 | 1,989 / 1,875 |
| SL(2,23) | 1/24 | 2.0 / 2.5 | 66 / 63 | 1,716 / 1,563 |
| SL(2,31) | 1/32 | 1.6 / 1.9 | 53 / 47 | 1,332 / 1,172 |

So R_j ≈ ρΔ(Δ−1)^{2j−1}/(4j) holds to within about 15 % at lengths 4 and 6. Length 2 runs at about 0.75 of it.

**What remains after the short cycles are gone** (`levels_by_class.py`, `out/levels_by_class_*.txt`): symmetric S
with no twisted *or* involutive 4- and 8-cycles, against random S with no involutive 4- and 8-cycles.
- SL(2,25): median cost 62 (115 samples) against 40 (2,043). That is a residual factor 1.55; the long-cycle term
  predicts e^{λ R₃ c₃} = 1.30.
- PSL(2,11)×Z24: 62 (60 samples) against 76 (1,129). Here the symmetric sets are *better* than random. On this group
  random S lose far more words than the Poisson model allows: median 91 against μ = 33, ε ≈ 2.7, against 1.8 on
  SL(2,25). Their ball at depth 5 is 130 elements short of Poisson, and the symmetric sets' only 45. Not explained.
- In clump terms both win clearly. A symmetric set's uncovered elements come in pairs, so 62 uncovered elements are
  31 independent misses, against 40 and 76.

### 3.2 Even D against odd D: the Anti targets

`order2/targets.py` splits each sample's uncovered elements into Fix(β), Anti(β) \ Fix, involutions, and the rest.
It bins the samples by their own generic miss rate p, then compares each class's miss rate with p (unpaired targets)
and with √p (targets whose words come in pairs, missed with probability e^{−λ/2}). Outputs: `out/targets/*.json`,
printed by `show_targets.py`.

| cell, group, involution | Anti miss rate / p (4 bins, best S first) | Anti / √p | Fix / √p |
|---|---|---|---|
| (6,8) SL(2,25), conjugation | 1.10, 1.10, 1.03, 1.01 | 0.06–0.30 | 0.89–1.06 |
| (6,8) PSL(2,11)×Z24, conjugation | 1.00, 1.01, 1.05, 0.98 | 0.06–0.37 | 0.91–1.02 |
| (6,8) SL(2,25), Frobenius | 1.38, 1.25, 1.16, 1.08 | 0.10–0.41 | 0.80–0.95 |
| (6,9) SL(2,25)×Z4, conjugation | 27, 17, 8.6, 3.3 | 0.69–0.85 | 1.0–1.7 |
| (6,9) SL(2,25)×Z4, Frobenius | 17, 9.3, 4.4, 1.9 | 0.48–0.70 | 0.87–0.97 |

- At even D the Anti elements are ordinary targets.
- At odd D they are missed at 0.5–0.85 × √p, close to the paired rate √p. The deficit is the σ-palindromic words: they
  all land in Anti and supply extra unpaired shots, about 750 for 516 Frobenius-Anti elements and for 2,596
  conjugation-Anti elements. That is why the deficit is larger for Frobenius.
- Fixed points are paired at both parities, as BEYOND_RANDOM had.

So at odd D an involution adds (2/k)·|Anti(β)|·e^{−λ/2} expected misses, unavoidably. For conjugation in SL(2,q)×Z_n,
|Anti| ≈ q²·|Anti_Z| and this is tens of misses at the records' sizes: 46–53 in the squad's odd-D cells, against
μ/2 ≈ 12–34 (`out/rule_table.txt`). It is the same mechanism as "PSL loses at odd D" (THRESHOLD Cor. 5.2, involution
targets). An involutive symmetry manufactures N/|Fix| such targets in any group.

*Second session:* the deficit below √p is quantitative. Palindromic words land on the image of the Lang map (2.8), so
only that part of Anti(β) gets the extra shots. With Z4 the bound of 2.2 is not tight, |Im L| = N/|Fix| is half of
|Anti|, and half of the Anti elements get no palindromes at all. That predicts 0.51·√p for Frobenius and 0.74·√p for
conjugation, against 0.48–0.70 and 0.69–0.85 measured (§3.5). For a tight, balanced involution the palindromes cancel
nearly the whole term (§3.5, §5.5).

### 3.3 Which assumption failed, in the brief's terms

| suspected assumption | verdict |
|---|---|
| the involution's fixed points | not the problem: \|Fix\|·e^{−λ/2} ≈ 1.1 at (6,8). Fixed points are paired as predicted (Fix/√p ≈ 0.8–1.06) |
| the Anti set | its size is right (tight uncertainty bound), but it enters twice. **At even D it matters only through twisted cycles, which are rare and avoidable when short. At odd D it is a set of extra targets**, unavoidable for conjugation-type involutions and nearly cancelled by palindromic words for tight balanced ones (§3.5). The old argument merged the two and treated the first as self-averaging |
| small Δ | yes, and this decides (6,8): at Δ = 6 order 3 has two orbits, and on SL(2,25) its space has 8,773 classes, none a solution (§3.4). The twisted 8-cycle mean ρΔ(Δ−1)³/8 ≈ 4 is also small enough to avoid |
| even D | yes for order 2: it removes the Anti-target term. For order 6 with a balanced involution, odd D is fine too (§5.5) |

The same error decided BEYOND_RANDOM's ranking of **Z6** (§4.2 there): "(Frobenius of order 2) × (conjugation of
order 3) … inherits the σ reflections, at rate about 1/q₀² … ranks it below plain k = 3".
- Its reflection penalty is the involution's twisted cycles again, treated as self-averaging. For a Frobenius
  involution ρ ≈ 1/q₀³, and they are cheap (§5.1).
- The other relation it cites, "x commutes with σ(x)", is a 6-cycle through the fixed letter e. Such a 6-cycle is rare
  and disappears with f = 0 or the OSUB layout.
- The order-6 Frobenius x ↦ x² of GF(64) is exactly such a Z6: its square has order 3 (x ↦ x⁴) and its cube is the
  Frobenius involution x ↦ x⁸. It beat order 3 by 5–35× in evaluations on the same group (§5.1).

### 3.4 Existence: counting the solution classes at (6,8) (second session)

Everything above is about typical sets. Whether a symmetry *can* win is a question about the extreme tail: does the
space contain a solution at all? At N = 15,600 the spaces are small enough to measure, and §2.7 turns the sample
counts into class counts. All on SL(2,25), (6,8), f = 0 (`runs/r2/`, `out/classes68/`; the order-3 sample of
2·10⁷ is STRUCTURE's `research/structured/runs/d6D8_sl_25_1_orb3f0_rand.log`):

| symmetry | symmetric sets | class size | classes | valid classes | P(valid) per set (−ln) | μ_A⁰ | avoid 4-, 8-cycles | μ_A⁰ + avoid − 6 | charged μ_A |
|---|---|---|---|---|---|---|---|---|---|
| SL(2,25), order 3, conjugation (two orbits of 3) | 1.348·10⁷ | 1,536 | 8,773 | **0** (best cost 2) | 0 | 12.9 | – | – | – |
| SL(2,25), order 2, Frobenius x ↦ x⁵ | 7.725·10¹⁰ | 28,800 | 2.68·10⁶ | **1** | 3.7·10⁻⁷ (14.8) | 20.2 | 0.84 | 15.0 | 22.0 |
| SL(2,25), order 2, conjugation (trace 0) | 7.870·10¹⁰ | 2,304 | 3.42·10⁷ | **≈ 40–60** | 1.7·10⁻⁶ (13.3) | 16.0 | 3.35 | 13.4 | 23.8 |
| PSL(2,11)×Z24, conjugation, z ↦ 11z | 8.239·10¹⁰ | – | – | – | 2·10⁻⁷ (15.4; 14.1–17.5) | 17.7 | 3.24 | 15.0 | 25.9 |
| PSL(2,11)×Z24, conjugation, z ↦ 23z | 8.239·10¹⁰ | – | – | – | < 3·10⁻⁷ (> 15.0); no set below cost 9 | 17.7 | 5.8 | 17.5 | 34.2 |

"avoid 4-, 8-cycles" is −ln P(a random symmetric set has no twisted 4- or 8-cycle), taken from the census of §3.1
(3.5 %, 3.9 % and 0.3 %) and from Poisson for Frobenius (R₁ + R₂ = 0.06 + 0.78).

How each entry was measured:
- **Order 3.** 10⁶ uniform samples (`runs/r2/nearmiss6_k3_sl25.log`). A class of 1,536 sets is hit Poisson(114)
  times, so every class is seen. Grouping the near misses by class (`classes68.trace_invariant`): one class at cost 2
  (126 hits), one at 3, two at 4, one at 5 and one at 6. Nothing at 0 or 1. STRUCTURE's 2·10⁷ samples agree (min 2;
  2,322 samples at cost 2 = the same single class). The cost-2 class leaves two fixed points of α uncovered. So no
  order-3 solution with f = 0 exists on SL(2,25). Every automorphism of order 3 is conjugate to this α, so this is a
  statement about the group, not about one α.
- **Frobenius.** 10⁷ uniform samples (`runs/r2/ro68_sl25_frob_1e7.log`): one solution. It and the five anneal
  solutions of §5.4 are one class: `symmetry68.py --to` finds two explicit maps T with T(S₁) = S₂ for every pair, and
  |Stab| = 2 for each (`out/classes68/sl25_frob_explicit_maps.txt`). Six independent draws all landing in one class
  make a single class by far the likeliest (two classes would give this with probability 1/32). One class means
  P(valid) = 28,800/7.725·10¹⁰ = 3.7·10⁻⁷. The direct count, 1 in 10⁷, is consistent with that (95 % interval
  2.5·10⁻⁹ to 5.6·10⁻⁷).
- **Conjugation.** 10⁷ uniform samples (`runs/r2/ro68_sl25_conj_1e7.log`, solutions in `…_dump.log`): 17 solutions in
  14 distinct classes. From P(valid) and the class size that is 58 classes; capture–recapture on 14 of 17 gives about
  40. The two anneal solutions s3 and s4 of §5.4 are different classes (no map between them), and the table-squad's
  record is one of the 14.
- **PSL(2,11)×Z24.** 10⁷ uniform samples for each r (`runs/r2/ro68_psl11x24_r{11,23}_1e7.log`). With r = 11:
  2 solutions, and 450 sets of cost ≤ 8. With r = 23, which doubles Anti and so the twisted-cycle density: no
  solution and no set below cost 9; p1 is 60 against 31.

What this shows:
1. **Order 3 lost at (6,8) because its space is too small, not because order 2 is cheap.** Per set, order 3 is better:
   its rate of sets with cost ≤ 6 is 6.8·10⁻⁴, against 1.6·10⁻⁴ for conjugation and 7·10⁻⁶ for Frobenius. Its
   space simply has 4,000 times fewer classes than conjugation's, and its rule value predicts 0.02 solution classes.
2. **The charge is half right.** One offset fits all four order-2 spaces:
   P(valid) ≈ P(no twisted 4- or 8-cycle) × e^{−(μ_A⁰ − 6)}. Measured against this model:
   conjugation 13.3 against 13.4, Frobenius 14.8 against 15.0, r = 11 15.4 against 15.0 (in −ln P), and r = 23 with
   0.25 expected hits and none seen. The short cycles are paid as avoidance, as the first session said. They are
   expensive, μ_A⁰λc_j ≈ 40 and 2 for 4- and 8-cycles, so a solution must have none or nearly none (§3.1). Two other
   things in the charged rule do not show:
   - the long cycles' charge, Σ_{cheap j} R_j(1 − e^{−x_j}) ≈ 4.5 nats for conjugation, 1 for Frobenius. With it,
     the fit spreads over 3 nats;
   - its absolute level: the Poisson baseline e^{−μ_A⁰} is about 6 nats too pessimistic at the extreme tail (item 3).

   On SL(2,25) the fixed points (120 against 24, 4.2 nats) outweigh the avoidance difference (2.5 nats). So conjugation
   has 4.6 times the solution density of Frobenius, the reverse of the charged rule's order.
3. **The lower tail is much fatter than Poisson.** Conjugation: P(cost 0)/P(cost 2) = 17/66 in the sample. A Poisson
   clump count with mean 16 would give 1/16. Frobenius: the one solution class is isolated, with no set of cost 1–3 in
   10⁷ samples and the next classes at cost 4. So e^{−μ_A} is a poor estimate of P(valid), here by about 6 nats. The
   effort law, calibrated on anneals, is a separate empirical statement.
4. **Anneal success is not existence.** The annealer found the single Frobenius class in 5 of 6 seeds and the ~50
   conjugation classes in 2 of 6 (§5.4). Plain random sampling finds a conjugation solution every 45 s, ten times
   faster than those anneals (2 in 900 s). For Frobenius the anneals were 4 times faster than sampling.

### 3.5 Odd D: palindromes cancel the Anti penalty of a tight involution (second session)

By 2.8, each Anti element in Im L gets π = P_ℓ|Fix(β)|/N single shots on top of its λ/2 paired ones. So it is missed
with probability e^{−λ/2−π}; Anti elements outside Im L are missed with e^{−λ/2}. Checks:

| case | \|Fix\|, \|Anti\|, \|Im L\| | P_ℓ | π on Im L | predicted Anti miss rate | measured |
|---|---|---|---|---|---|
| (6,9) SL(2,25)×Z4, Frobenius | 240, 516, 260 | 936 | 3.6 | 0.51 √p (half of Anti in Im L) | 0.48–0.70 √p (§3.2) |
| (6,9) SL(2,25)×Z4, conjugation | 48, 2,596, 1,300 | 936 | 0.72 | 0.74 √p | 0.69–0.85 √p |
| (12,7) SL(2,64), α³ = Frobenius x ↦ x⁸ (order 6) | 504, 520, 520 (tight, balanced) | 1,596 | 3.07 | 1.9 × generic | 1.7 × generic (`runs/r2/classes127_sl64_k6frob.log`, best 10 % of 600) |

Without the palindromes the last row would be 41 × generic. For a tight balanced involution the Anti term of the
rule becomes (2/k)·√N·e^{−λ/2−π} ≈ (2/k)·√μ·e^{−√λ}. That is the first session's term times e^{−√λ}: 0.07 at (12,7)
(λ = 7.4), 0.02–0.03 at the D = 9 record sizes (λ ≈ 13–16). The cost left is the fixed points of the involution, (2/k)·|Fix(β)|·e^{−λ/2},
which is (2/k)√μ when balanced. So at odd D:
- order 2: μ/2 + √μ at best, always worse than order 3's μ/3;
- order 6: μ/6 + (1/3)√μ + small fixed-point terms, better than order 3 once μ ≳ 15.

## 4. The corrected rule

Second-session form. For α of order k with α(S) = S, f fixed generators and m orbits of size k:

    μ_A ≈ μ/k  +  Σ_{1 ≠ H ≤ ⟨α⟩} #{x : Stab(x) = H}·(|H|/k)·e^{−λ/|H|}
               +  [D odd]·Σ_{involutions β ∈ ⟨α⟩} (2/k)·( |Anti(β) ∩ Im L_β|·e^{−λ/2−π_β} + |Anti(β) \ Im L_β|·e^{−λ/2} )

with π_β = P_ℓ·|Fix(β)|/N palindromic shots (§2.8, §3.5). Anti(β) is taken outside Fix(β), and
|Im L_β| = N/|Fix(β)|. Then:
- **Ranking.** Among symmetries whose spaces are large enough, prefer the smallest μ_A, and estimate the anneal
  effort with the effort law. On the twelve odd-D screens of `out/rule_table2.txt` the measured p1 is 1.2–1.7 times
  μ_A, and the order is always right.
- **Existence.** The space must contain a solution: roughly ln(#classes) − μ_A ≳ 0, with
  #classes = #S·|Stab(S)|/|N_E(⟨α⟩)| (§2.7). This is what decided (6,8): order 3 has ln 8,773 = 9.1 against
  μ_A = 12.9, order 2 has ln(3.4·10⁷) = 17.3 against 16.0 (§3.4). The absolute value of e^{−μ_A} is off by several
  nats at (6,8) (2.7 and 5.4 too pessimistic for the two order-2 spaces). So treat this as a screen, and where N is
  small, count instead: sample the space and group the near misses into classes.
- **Twisted cycles** (even and odd D, any involution in ⟨α⟩). A solution keeps n* = R_j·e^{−μ_A⁰λc_j} twisted
  4j-cycles, where R_j = ρ_β Δ(Δ−1)^{2j−1}/(4j) and c_j = 2j(ℓ−2j+1)/(Δ(Δ−1)^{2j−1}) (§3.1). This holds on 6 anneal
  solutions and 17 uniform ones. Charge the families with x_j = μ_A⁰λc_j ≳ 1 their avoidance price,
  −ln P(no such cycle), which is ≈ Σ R_j for Poisson counts (§3.4). Do not charge the cheap long families: the first
  session's R_j(1 − e^{−x_j}) for them (≈ 4.5 nats for conjugation at (6,8)) is not seen in the solution counts.
  `rule.py` still prints the first session's full charge (column gfnat), and its table (`out/rule_table.txt`) is
  unchanged.

`order2/rule.py` implements both forms: `python3 rule.py` prints the first session's 24 cases (`out/rule_table.txt`)
and `python3 rule.py --second` the odd-D cases with the palindrome term (`out/rule_table2.txt`).

In words:

1. Clumps of size k divide μ by k (BEYOND_RANDOM).
2. Each subgroup H of ⟨α⟩ pays for its fixed points at rate e^{−λ/|H|}. This is bounded for Frobenius-type α on
   SL(2,p^e) for every e, and for k = 2, 3 conjugation in SL(2,q).
3. **Odd D:** every involution β in ⟨α⟩ also pays for its Anti elements, at e^{−λ/2} each, except where the
   palindromic words cover them. Those land on Im L_β, giving π ≈ √λ shots each when β is tight and balanced
   (|Fix| ≈ |Anti| ≈ √N).
   - Conjugation-type involutions of SL(2,q)×Z_n are far from balanced: |Anti| ≈ q²·|Anti_Z|, so π ≪ 1 and the term
     kills the method.
   - Frobenius-type or swap-type involutions with a balanced cyclic part pay only their fixed points,
     (2/k)|Fix(β)|e^{−λ/2} ≈ (2/k)√μ.
   - So order 2 never beats order 3 at odd D (μ/2 + √μ > μ/3), but **order 6 does** (μ/6 + √μ/3 < μ/3 once μ ≳ 15).
     The first session's "with k = 3 available, no even order should be used at odd D" is withdrawn for k ≥ 6.
4. **Even D:** no Anti term. An involution's twisted cycles are a Poisson field with means R_j ∝ ρ(Δ−1)^{2j}.
   Solutions avoid the short ones, which costs −ln P(none) ≈ Σ_{short} R_j. The long ones are free.
5. **Space:** a symmetry is usable only if its orbit space has enough classes (existence condition above). At small
   Δ and small N this, not μ_A, decides. That is why order 2 beat order 3 at (6,8).

How well it predicts:
- `out/rule_table.txt`: every odd-D k = 2 failure in the squad logs gets μ_A ≫ μ (96–136 against μ = 25–67). Every
  even-D k = 2 failure outside (6,8) gets μ_A 1.8–3.2 times the order-3 value at the same cell and order: (6,10),
  (7,8), (8,8), (9,8). The order-6 runs at (13,8) are predicted to within their scatter.
- `out/rule_table2.txt`: at odd D the rule orders order 6 < order 3 < order 2 < random correctly on SL(2,64) and
  SL(2,8)² at (12,7), and order 6 < order 3 on SL(2,64)×Z403 at (15,9).
- At (6,8) the absolute level e^{−μ_A⁰} is about 6 nats pessimistic. With the short-cycle avoidance price and that one
  offset, the rule fits all four order-2 spaces to within 0.4 nats (§3.4).

### 4.1 Choosing a symmetry: a checklist for future searches

1. **Odd D:** odd k (3, or 5 with small fixed sets), or k ≥ 6 whose involution β is tight and balanced
   (|Fix(β)|·|Anti(β)| = N with both near √N). The palindromes then cover Anti(β) (§3.5). Never k = 2. On Z_n,
   balance means α^{k/2} fixes one part and negates another of about the same size. Example: Z403 = Z13×Z31 with r of
   order 3 mod 13 and order 6 mod 31, so α³ fixes Z13 and negates Z31.
2. **Even D:** any k. For every subgroup H ≤ ⟨α⟩, count the elements whose stabiliser is exactly H. Each costs
   (|H|/k)·e^{−λ/|H|}, the miss rate p^{1/|H|} checked in §5.1.
3. For every involution β ∈ ⟨α⟩, compute ρ = |Anti(β)|/N (≥ 1/|Fix(β)|). Then:
   - at small Δ (6–8), keep the twisted 8-cycle mean ρΔ(Δ−1)³/8 at a few or less;
   - at large Δ (≥ 12) twisted cycles are cheap anyway (c_j tiny).
   - Prefer β with a large centralizer and a tight uncertainty bound. For Z_n, choose r so that
     gcd(r−1, n)·gcd(r+1, n) = n (for n = 24 that is r = 11, not −1).
4. **Large k with small fixed sets** comes from:
   - Frobenius of order e on SL(2,p^e): fixed sets SL(2,p^d) for d | e;
   - swap∘(automorphism of order k/2) on G×G, where α^{k/2} fixes a twisted diagonal ≅ G.

   Conjugation in SL(2,q) has |Fix| ≈ q at every level, which blocks k ≥ 5 (STRUCTURE §2.3).
5. **Fill Δ with free orbits plus at most one smaller α-orbit (`OSUB`)** instead of fixed letters. Fixed letters
   come from Fix(α), which for Frobenius or swap types is a small non-abelian group full of involutions and
   order-3 elements.
6. **Z_n factor:** r must have the full order k modulo every prime of n, and every power α^j (j < k) must move every
   cyclic quotient. Primes p ≡ 1 mod k work; Z9 does not for k = 6 (its order-3 automorphisms fix Z3); Z2 is harmless.
   Avoid large cyclic factors next to a small simple group (SL(2,5)²×Z247 and SL(2,16)×Z145 screen 3–6× worse than
   the rule's μ_A).
7. **When N is small, count the space before trusting μ_A** (second session). Sample 10⁶–10⁷ symmetric sets,
   group the near misses into classes (`classes68.py`), and compare #classes with the near-miss classes found. At
   (6,8) this showed that order 3 has no solution at all on SL(2,25) (§3.4).
8. **Screen before annealing:** RANDORB's lower tail in clump units (cost/k) ranks candidates the way the anneals
   did. All runs of this session (random-symmetric p10 from 60–200 samples; the rule's μ_A; anneal outcome):

   | cell, group, order | p10 / k | rule μ_A | anneals |
   |---|---|---|---|
   | (13,8) SL(2,64)×Z13, 6 | 6.2 | 7.9 | 3/3 solved, 4.7·10³–3.7·10⁴ |
   | (15,8) PSL(2,137)×Z7, 3 (record group) | 7.7 | ≈ 11 | solved, 7.8·10⁴ (STRUCTURE) |
   | (13,8) SL(2,7)²×Z31, 6 | 9.5–10.7 | 11.0 | 1/9 solved, 1.3·10⁵ |
   | (15,8) SL(2,8)²×Z37, 6 + OSUB 3 | 10.7 | 10.4 | RESULT-158 |
   | (13,8) SL(2,64)×Z13, 3 | 9–11 | 13.2 | 1/1 solved, 1.7·10⁵; Frobenius 0/1 at 2.6·10⁵ |
   | (13,8) PSL(2,13)²×Z3, 6 | 15.2 | 14.7 | 0/2, best 8 and 21 at 1.1–1.5·10⁵ |
   | (13,8) SL(2,8)²×Z14, 6 | 16–17 | 15.0 | 0/6, best 18–26 at 2–6·10⁴ |
   | (13,8) SL(2,64)×Z14, 6 | 21.7 | 20.9 | not run |

   p10/k and the rule's μ_A agree to within a factor of about 1.25, and both order the outcomes. The rule misses mixing
   defects that the screen catches (large cyclic factors; footnote in §5.2).

## 5. Predictions and tests

### 5.1 Even orders beat order 3 at even D when the involution has a large centralizer

On SL(2,64) the Frobenius F: x ↦ x² of GF(64) has order 6. Its powers fix SL(2,2), SL(2,4) and SL(2,8) (orders 6,
60, 504). Its involution F³ has ρ = 520·13/N ≈ 1/504, so its twisted cycles are negligible. With z ↦ 4z on Z13
(order 6), the rule gives μ_A = 35.5/6 + 2.0 = 7.9, about 10⁴ evaluations. Order 3 gives μ_A = 13.2, about
1.1·10⁵. haar_inv's AFROB=1 already implements this α. Cell (13,8), group SL(2,64)×Z13, the current record order:

| symmetry | seeds | evaluations to solve | source |
|---|---|---|---|
| order 3, conjugation (ORBIT="3 4 1") | 1 | 170,313 (1,661 s) | BEYOND_RANDOM `exp/an_138_sl64_conj.log` |
| order 3, Frobenius x ↦ x⁴ | 1 | not solved, best 1 after 256,889 | BEYOND_RANDOM `exp/an_138_sl64_frob.log` |
| **order 6, Frobenius x ↦ x² (ORBIT="6 2 1" AFROB=1 AR=4)** | 3 | **4,665, 9,625, 37,185** (30, 62, 236 s) | `order2/runs/an138_sl64_13_k6frob_s*.log` |

Random symmetric samples on the same group give the same ranking, per clump (`runs/ro138_*.txt`, 60 samples each):

| symmetry | min | p10 | median raw cost |
|---|---|---|---|
| order 3, conjugation | 18 | 33 | 49 |
| order 3, Frobenius | 18 | 28 | 50 |
| order 6 | 24 | 37 | 75 |
| order 2, Frobenius x ↦ x⁸ | 26 | 37 | 56 |

Divided by the clump size, order 6 is lowest: its p10 is about 6 clumps, against 9–11 for order 3 and 18 for
order 2.

All three order-6 solutions passed haar_sym's full diameter check (`sols/d13D8_sl_64_13_orb6frob_s*.txt`). They have
the record's order, so they are not records. `check_np.py` confirms all three (VALID, diameter 8;
`checks/d13D8_sl_64_13_orb6frob_s*.check_np.txt`).

**The fixed-point term at every level.** haar_order2's `CLASSES=1` mode samples random symmetric S and records which
stabiliser class each uncovered element is in. The model says an element whose stabiliser in ⟨α⟩ has order h is
missed with probability p^{1/h}, where p is the free elements' rate. Samples are binned by their own p, best quartile
first, and each entry is measured / predicted (`out/classes/summary.txt`):

| group, symmetry (cell) | h = 2 | h = 3 | h = 6 | free ∩ Anti(α^{k/2}) / p |
|---|---|---|---|---|
| SL(2,64)×Z13, Frobenius order 6 (13,8) | 1.10, 0.91, 0.77 (498 el.) | 1.21, 0.92, 0.90 (54) | 0.91, 0.89, 0.74 (6, incl. e) | 2.8, 2.0, 1.2 |
| SL(2,7)²×Z31, swap∘conj order 6 (13,8) | 0.91, 0.79, 0.67 (330) | 0.98, 1.00, 1.03 (30) | 0.60, 0.51, 0.45 (6, incl. e) | 2.4, 1.6, 1.7 |
| SL(2,64)×Z13, conjugation order 3 (13,8) | – | 1.05, 0.96, 0.94 (63) | – | – |
| SL(2,25), conjugation order 2 (6,8) | 0.99, 0.97, 1.00 (24) | – | – | 1.12, 1.06, 1.06 |
| SL(2,25)×Z4, conjugation order 2 (6,9) | 1.63, 1.48, 1.16 (48) | – | – | 30, 19, 9.6 (0.84, 0.77, 0.74 of √p) |

- The p^{1/h} law holds to within 10–30 % at h = 2 and 3.
- At h = 6 the class has only six elements, and e is one of them. e is always covered (it is a generator), and the
  swap∘conjugation fixed points (a diagonal torus) are covered more often than predicted. That makes the term smaller,
  not larger.
- The free elements of Anti(α³) are missed 1.2–2.8 times more than generic ones even at even D. This is a small class
  (0.2–0.3 % of G), and the effect is not explained. It costs less than 0.01 expected misses at these sizes.

**The order-6 solutions keep cheap twisted cycles** (`twist.py sol … --frob 3` or `--swapconj`;
`out/census_d13D8_*.json`).
- On SL(2,64)×Z13 (seed 2) the involution α³ = (x ↦ x⁸, z ↦ −z) fixes 504 elements and |Anti(α³)| = 6,760, so
  ρ = 1/504. The solution has
  - 0 twisted 4-cycles (expected 0.08);
  - 12 twisted 8-cycles (expected 5.6);
  - 605 twisted 12-cycles (expected 535).
- The record graph on SL(2,7)²×Z31 (ρ = 1/336, tight: 336 × 10,416 = N) has 0, 9 and 665, against expected 0.12, 8.4
  and 800.
- At Δ = 13 a twisted 8-cycle costs only λc₂ ≈ 0.008 in ln cost, so the search has no reason to avoid it. Its ball at
  depth 4 is short of the maximum by 48 elements on SL(2,64): exactly the 12 twisted 8-cycles × 4 pairs.
- At Δ = 6 an 8-cycle costs 0.13, and both (6,8) records have none.

So the search avoids twisted cycles exactly when they are expensive, as the rule assumes.

### 5.2 Record attempts at (13,8) with order 6 (current record 6,814,080 = 2 × 3,407,040)

New automorphisms in `order2/src/haar_order2.c` (haar_inv plus two modes):
- AFSWAP=j: (x₁, x₂) ↦ (F^j(x₂), x₁) on G×G.
- ASWAPC=1: (x₁, x₂) ↦ (c x₂ c⁻¹, x₁).
Both have order 2·ord(F^j) or 2·ord(conj c). The involution α³ fixes a diagonal copy of G, so ρ ≈ 1/|G|.

| group | N (vs record) | α | μ | μ_A (rule) | random symmetric: min, p10 | anneals |
|---|---|---|---|---|---|---|
| **SL(2,7)²×Z31** | **3,499,776 (+2.7 %)** | swap∘conj(order 3), z ↦ 6z | 49.4 | 11.0 | 35, 64 | **seed 2 solved in 131,625 evaluations (741 s)**; seeds 1, 3–8: best 6 (one orbit) after 3–14·10⁴ |
| SL(2,8)²×Z14 | 3,556,224 (+4.4 %) | swap∘Frobenius (x ↦ x² or x⁴), z ↦ 3z or 5z | 59.9 | 15.0 | 60–72, 97–104 | 6 seeds of 300–900 s: best 18–26 |
| SL(2,64)×Z14 | 3,669,120 (+7.7 %) | Frobenius order 6, z ↦ 3z | 86.7 | 20.9 | 70, 130 | not run (≈ 5·10⁶ evaluations by the rule) |
| PSL(2,13)²×Z3 | 3,577,392 (+5.0 %) | swap∘conj(order 3), z ↦ 2z | 64.3 | 14.7 | 52, 91 | 2 seeds of 1,300–1,800 s: best 8 and 21 (1.1–1.5·10⁵ evaluations) |
| PSL(2,7)²×Z126 | 3,556,224 (+4.4 %) | swap∘conj(order 3), z ↦ 5z | 59.9 | 11.5* | 57, 132 | screen only: no order-6 multiplier of Z9 moves Z3, and the large cyclic factor mixes badly |
| SL(2,5)²×Z247 | 3,556,800 (+4.4 %) | swap∘conj(order 3), z ↦ 69z | 60.0 | ≈ 11* | 108, 364 | screen only: the large cyclic factor mixes badly |

\* The rule's μ_A counts only clumps, fixed points and twisted cycles. It does not see the poor mixing of a large
cyclic factor with a small simple group (STRUCTURE §5). The random-symmetric screen does, and it is the better guide
there.

**The record graph.** `sols/d13D8_prod_sl_7_sl_7_31_orb6swc_s2.txt`, also in `research/frontier/sols/`:
- S = {e} ∪ O₁ ∪ O₂ in SL(2,7) × SL(2,7) × Z31, with O_i = {s_i, α(s_i), …, α⁵(s_i)};
- c = mat(2,0,4,4), of trace −1 and order 3;
- 3,499,776 group elements, so 6,999,552 vertices.

The four checks:
- haar_order2's full diameter check (all four side pairs within 8): OK.
- `research/frontier/build_haar2.py`, which rebuilds the group from its definition: ecc 8 from both sides, nothing
  unreached, 45,497,088 edges, every degree 13, no repeated edge, edge-list sha256
  daf0ccf91e35dc587d6bed076ba05be225de3cd0aa2c4607032cffe86af6ebb2. VALID
  (`checks/d13D8_prod_sl_7_sl_7_31_orb6swc_s2.check.txt`).
- `check_np.py`, a third group implementation: BFS from (e,A) and (e,B) over all 6,999,552 vertices, ecc 8 from both,
  nothing unreached, 13 distinct generators. VALID (`checks/…check_np.txt`).
- `check_lowmem.c`, a fourth, written in C from scratch (own field and matrix arithmetic, bitset BFS): VALID, ecc 8
  from both sides (`checks/…check_lowmem.txt`). It reports INVALID (ecc 9) on a near miss with 12 uncovered.

apsp.c is out of reach at 7M vertices (about n²·d/64 ≈ 10¹³ operations). Right multiplication is transitive on each
side, so the two BFS determine the diameter.

The effort was about 4× the rule's median estimate (one solve in 8 seeds, at 1.3·10⁵ evaluations against
3.6·10⁴). That is within the effort law's factor-5 scatter, but on the slow side, like the product group SL(2,8)²×Z14.

What order 6 bought on this group (random symmetric samples, 200 each, `runs/ro138_sl7sq_31_k3_vs_k6.txt`):

| symmetry | min | p10 raw | p10 in clumps | rule μ_A |
|---|---|---|---|---|
| order 3, conjugation by (c, c′), z ↦ 5z | 25 | 51 | 17 | 17.3 |
| order 6, swap∘conjugation, z ↦ 6z | 30 | 57 | 9.5 | 11.0 |

By the effort law that is 20–40× fewer evaluations for order 6 on the same group.

### 5.2b Mixed orbit sizes: (15,8) and the open cell (10,8)

The fixed-point analysis suggests a further layout. An element whose α-orbit has size s < k (it lies in Fix(α^s)) can
be a generator too: S = (m free orbits of size k) ∪ (one orbit of size s), so Δ = km + s with no fixed letter at all.
This changes the orbit space, not the clumps: the uncovered set is ⟨α⟩-invariant whatever S's orbit sizes are, and
the class costs of §5.1 are unchanged. It avoids the bad fixed letters that make f = 3 weak (abelian triples,
involutions and order-3 elements in Fix(α); BEYOND_RANDOM §1.4). haar_order2 implements it as `OSUB=s`.

| cell | group, α, layout | N (vs our record) | μ | μ_A (rule) | random symmetric: min, p10 (clumps) | result |
|---|---|---|---|---|---|---|
| (15,8) | SL(2,8)²×Z37, swap∘Frobenius, z ↦ 27z; 6 + 6 + 3 (`ORBIT="6 2 0" OSUB=3`) | 9,398,592 (+4.4 %) | 53.4 | 10.4 | 37, 64 (10.7) | RESULT-158 |
| (15,8) | PSL(2,137)×Z7, conjugation order 3; 3·5 (record group, for comparison) | 8,999,256 | 29.9 | ≈ 11 | 12, 23 (7.7) | solved in 7.8·10⁴ (STRUCTURE) |
| (10,8) open | SL(2,16)×Z145, Frobenius x ↦ x² (order 4), z ↦ 12z; 4 + 4 + 2 | 591,600 (table 588,240) | 66.4 | 17.5 before the twisted penalty | 152, 356 (89) | dead: α² fixes only SL(2,4), so ρ = 1/60 and 15 unavoidable twisted 8-cycles at Δ = 10; plus a large cyclic factor |
| (10,8) open | SL(2,16)×Z146 and ×Z149, the same | 595,680 / 607,920 | 71 / 87 | – | 220–494 | dead |
| (10,8) open | PSL(2,23)×Z97, conjugation order 3 (STRUCTURE's attempt) | 588,984 | 63.5 | 22 | 36, 78 (26) | best 12 in STRUCTURE |

### 5.4 The direct test at (6,8): which involution, and does the twisted-cycle charge count?

Four order-2 symmetries at (6,8), 6 seeds each, 150 s per seed (`runs/d68_compare.sh`, logs in `runs/d68/`,
`d68_summary.py` → `out/d68_summary.txt`; every solution VALID by `check_np.py`,
`checks/d68_compare_solutions.check_np.txt`). The two columns of rule predictions differ only in the twisted-cycle
term. "μ_A⁰" is without it, and "+ charge" adds the generating-function charge Σ R_j(1 − e^{−μ_A⁰λc_j}) of §3.1
(`out/rule_table.txt`, column gfnat). PSL(2,11)×Z24 evaluates about 3.3× faster than SL(2,25) (wide rows), so in
150 s it gets about 12M evaluations against 3.7M, worth about 2.4 nats of μ_A by the effort law.

| symmetry | ρ | \|Fix\| | μ_A⁰ | μ_A⁰ + charge | solved in 150 s | evaluations to solve | best of the unsolved |
|---|---|---|---|---|---|---|---|
| SL(2,25), Frobenius x ↦ x⁵ | 1/120 | 120 | 20.2 | **22.0** | **5/6** | 0.13, 0.29, 0.42, 0.49, 2.4 M | 4 |
| SL(2,25), conjugation (trace 0) | 1/24 | 24 | **16.0** | 23.8 | 2/6 | 0.07, 0.36 M | 2, 1, 2, 2 |
| PSL(2,11)×Z24, conjugation, z ↦ 11z | 1/23.6 | 24 | 17.7 | 25.9 (≈ 23.5 per second) | 2/6 | 0.46, 0.68 M | 2, 3, 2, 2 |
| PSL(2,11)×Z24, conjugation, z ↦ 23z | 1/11.8 | 24 | 17.7 | 34.2 | 0/6 | – | 11, 6, 11, 11, 12, 11 |

- **The ranking is the charged one.** Frobenius first, then conjugation and r = 11 together, with r = 23 far behind.
  Without the charge, conjugation should have been easiest (lowest μ_A⁰) and Frobenius hardest: its 120 fixed points
  cost 5 nats more. The opposite happened, 5/6 against 2/6 on the same group with the same budget.
- So at Δ = 6 the twisted cycles of a small-centralizer involution cost real effort, although no solution contains a
  short one. The cost is the avoidance itself (the search must find S in a 4 % class) plus the long cycles.
- The Z_n choice matters as predicted: r = 23 doubles ρ and never solves, while r = 11 does.
- This settles the open item of §4. The rule with the charge predicts the effort ranking. The two earlier (6,8) solves
  that looked too fast were early draws: here r = 11 solved 2 of 6 seeds, in 0.46M and 0.68M evaluations, and
  stalled at 2–3 in the other four after 12M.

**Second session: the same four spaces counted directly** (§3.4, 10⁷ uniform samples each):

| symmetry | anneal: solved in 150 s | solutions in 10⁷ samples | P(valid) | classes |
|---|---|---|---|---|
| SL(2,25), Frobenius | 5/6 | 1 | 3.7·10⁻⁷ (one class) | 1 (all six solutions found are one class) |
| SL(2,25), conjugation | 2/6 | 17 | 1.7·10⁻⁶ | ≈ 40–60 (14 distinct among the 17) |
| PSL(2,11)×Z24, r = 11 | 2/6 | 2 | 2·10⁻⁷ | – |
| PSL(2,11)×Z24, r = 23 | 0/6 | 0 (min cost 9) | < 3·10⁻⁷ | – |

- The anneal and the counts agree that r = 23 is far worse than r = 11, and that the twisted cycles cost something.
- They disagree on Frobenius against conjugation. Conjugation has 4.6 times the solution density, and plain sampling
  finds its solutions ten times faster than these anneals did.
- So the first bullet above overstates: 5/6 against 2/6 is not significant (Fisher p = 0.12), and the charged rule's
  order for these two is wrong as a statement about solutions. The model that fits all four (§3.4) charges only the
  avoidance of short cycles.
- Which annealer behaviour favours the lone Frobenius class (it has no near misses at cost 1–3, while conjugation has
  118 per 10⁷) is left open.

### 5.3 Where else order 2, or another even order, should win

By the rule (second-session form), an even order beats order 3 in one of two ways:
- **order 2**, at even D only, where the order-3 space is starved. Two orbits at small N leave too few classes to
  contain a solution (§3.4). The involution's 8-cycles must also be avoidable: R₂ = ρΔ(Δ−1)³/8 ≲ 5, i.e.
  |Fix(β)| ≳ 20, 40, 70 for Δ = 6, 7, 8;
- **order 6 or more**, with bounded fixed-point costs (Frobenius or swap type, checklist §4.1), at even D, or at odd D
  if the involution α^{k/2} is tight and balanced (§3.5, §5.5).

Going through the table:
- **Order 2:** only (6,8). At (6,10), (7,8), (8,8) and (9,8) order 3 has room. There μ/2 against μ/3 is 2–8 nats of
  μ_A, which matches the squad's failures (`out/rule_table.txt`). At odd D: never (μ/2 + √μ > μ/3 even with
  palindromes, §3.5).
- **Order 4:** needs a Frobenius of order 4 (SL(2,16), SL(2,81)) or conjugation by an element whose square has a
  large centralizer. Near the records, the cyclic factors either have no automorphism of order 4 (primes ≡ 3 mod 4)
  or leave α² trivial on them, which puts thousands of elements in Fix(α²). Checked by hand: (8,8), (9,8), (8,10),
  (9,10), (10,10), (13,8). The only clean one is (10,10) on SL(2,81)×Z58, and there μ_A ≈ 7.6 equals order 3's. No
  gain predicted.
- **Order 6:** needs Δ ≥ 12 for two orbits.
  - (12,8), (14,8) and (16,8) are above the first-moment ceiling even with μ/6.
  - (13,8): done (§5.2), and (15,8) with the mixed layout 6+6+3 (§5.2b).
  - Odd D, Δ ≥ 12: (15,9) on SL(2,64)×Z403 and (13,9) on SL(2,64)×Z133 (§5.5).
  - The D = 10 cells need groups of order about 10⁸–10⁹. The Frobenius type SL(2,729) is 16 % too big for (13,10),
    but the swap type fits: SL(2,16)²×Z21, below.
- **Order 8 and up:** needs Δ ≥ 16 for two orbits; no candidate group.
- **(13,10) on SL(2,16)²×Z21**, with α = swap∘conj(order 3) × (z ↦ 5z), r of order 6 (Z21 = Z3 × Z7). The
  random symmetric screen (16 samples, `runs/ro1310_sl16sq_21_k6.txt`) gives min 23 and p10 26 at μ = 35.5. That is
  4.3 clumps, better than SL(2,64)×Z13 (6.2), which solved in about 10⁴ evaluations. The first session's anneal was
  cut off. Second session: RESULT-1310.
  - N = 349,574,400, so 699,148,800 vertices, +3.2 % over the current record 677,714,400 (+4.7 % over the
    667,903,200 of the first session).
  - μ = 36.4. The rule gives μ_A ≈ 9.1 for order 6 (fixed points 3.0) against ≈ 13 for order 3 at the same N, which is
    about 7× fewer evaluations.
  - The effort law predicts about 1.4·10⁴ evaluations. At about 1.2 s each (the (13,10) record run took 1.1 s per
    evaluation at N = 3.3·10⁸) that is 5–20 hours on one core, beyond this session.

### 5.5 Odd D: order 6 against order 3 (second session)

**Prediction** (§3.5, §4): at odd D, an order-6 symmetry whose involution is tight and balanced has fewer uncovered
clumps than order 3, because the palindromes remove its Anti penalty. Order 2 stays worse than order 3.

**Screens.** Random symmetric sets; cost = uncovered elements on both sides; clumps = cost/2k. The rule column is
`rule.py --second` (`out/rule_table2.txt`). Logs: `runs/r2/ro127_*.log`, `ro149_*.log`, `ro159_*.log`. Samples per
row: 3,000 at (12,7), 40 at (14,9), 16 at (15,9).

| cell, group (N; μ) | symmetry | rule μ_A | min | p1 | p10 (clumps) |
|---|---|---|---|---|---|
| (12,7) SL(2,64) (262,080; 154.6) | order 6, Frobenius x ↦ x² | 34.0 | 26.2 | 41.7 | 57.6 |
| | order 3, Frobenius x ↦ x⁴ | 56.5 | 66.2 | 75.2 | 92.8 |
| | order 3, conjugation | 56.7 | 61.3 | 79.5 | 98.3 |
| | order 2, Frobenius x ↦ x⁸ | 90.0 | 124 | 144.5 | 180 |
| | random | 154.6 | 223 | 247 | 278.5 |
| (12,7) SL(2,8)² (254,016; 118.3) | order 6, swap∘conj | 28.7 | 27.0 | 35.6 | 50.3 |
| | order 3, conjugation (c, c′) | 45.6 | 53.0 | 69.3 | 87.5 |
| | order 2, swap | 70.4 | 99 | 118 | 153 |
| | random | 118.3 | 175 | 202 | 232 |
| (14,9) PSL(2,25)² (60,840,000; 29.9) | order 6, swap∘conj, f = 2 | – | 15.0 | – | 19.3 |
| | order 3, conjugation, f = 2 | – | 29.5 | – | 35.0 |
| (15,9) SL(2,64)×Z403 (105,618,240; 30.8) | order 6, Frobenius, 6+6+3 | 7.2 | 3.2 | – | 6.3 |
| | order 3, Frobenius x ↦ x⁴ | 10.7 | 10.3 | – | 13.8 |

- In every pair, order 6 has about half the clumps of order 3 (ratio 0.45–0.56 at p1 or p10). The measured order is
  the rule's in every group.
- The first session's Anti term would have added 3–11 clumps to each order-6 row. Measured, they carry less than one.
- The product group PSL(2,25)² mixes poorly at (14,9): the order-3 median, 242, is 4× the Poisson value. So it is no
  candidate, although its order is +4.8 % over the record.

**Candidates near the D = 9 records** (balanced involution, Δ ≥ 12; rule values from `rule.py`):
- **(15,9) SL(2,64)×Z403**, Z403 = Z13×Z31, z ↦ 367z (order 3 mod 13, order 6 mod 31). N = 105,618,240, so
  211,236,480 vertices, +1.5 % over 208,029,120. Order 6, μ_A = 7.2, about 5·10³ evaluations; order 3, μ_A = 10.7.
  Anneal: RESULT-159.
- (13,9) SL(2,64)×Z133, Z133 = Z7×Z19, with α³ fixing Z7 and negating Z19. +2.9 %, μ = 49.9. Order 6, μ_A = 11.0,
  about 4·10⁴ evaluations; order 3, μ_A = 17.3, about 8·10⁵. The record group SL(2,103)×Z31 has μ_A = 12.0 with
  order 3, so this is predicted easier than the record was, at a larger N.
- (14,9) PSL(2,25)²: +4.8 %, but poor mixing (above).
- (12,9) and (16,9): no tight balanced group found within +10 % of the record.

## 6. Ranked conclusions

(Both sessions. "S2" marks what the second session added or changed.)

**Proved**
1. Reflection lemma: an involutive symmetry's coincidences are exactly the twisted cycles v·σ(v), v ∈ Anti(β) (§2.1).
   Their expected number per length is ρ × (number of words) up to the words without a singleton orbit (§2.6).
2. |Fix(β)|·|Anti(β)| ≥ N, tight for trace-0 conjugation in SL(2,q) and for Frobenius of order 2 on SL(2,q₀²);
   z ↦ −z on Z_n with n even is not tight (§2.2).
3. At odd D, β* = inversion∘β is a symmetry of each side's binding multiset, so Anti(β) consists of β*-fixed targets.
   At even D it is not a symmetry (§2.3).
4. |Fix| + |Anti| ≥ 2√N (§2.4).
5. S2. Classes: valid symmetric sets come in classes of equivalent Haar graphs, of size |N_E(⟨α⟩)|/|Stab(S)| (§2.7).
   At (6,8) on SL(2,25) the sizes are 1,536 (order 3), 2,304 (conjugation, order 2) and 28,800 (Frobenius, order 2),
   by count and by brute force.
6. S2. Palindromes: σ-palindromic words take values in the Lang image {β(x)⁻¹x}, of size N/|Fix(β)| ⊆ Anti(β) (§2.8).
7. S2, by computer:
   - the six Frobenius-symmetric solutions found at (6,8) on SL(2,25) (five anneals, one uniform sample) are one
     class, by explicit maps;
   - every (6,8) solution examined has only the symmetries {1, β};
   - the conjugation solutions s3 and s4 are different classes.
8. S2, by complete census (sampling). There is no order-3-symmetric (f = 0) solution at (6,8) on SL(2,25). A
   full-size class (1,536 sets) is hit about 114 times in 10⁶ uniform samples, so the chance of missing one is below
   10⁻⁴⁰. A class with extra symmetry is smaller but still hit ≥ 57 times if its stabiliser has order ≤ 6. The best
   class has cost 2 (§3.4).

**Conjectured with strong evidence**
1. S2. **Why order 2 beat order 3 at (6,8):** order 3's space is too small (item 8 above). It holds 8,773 classes,
   against 2.68·10⁶ for the Frobenius involution (1 valid) and 3.42·10⁷ for the conjugation involution (≈ 40–60
   valid). Per set, order 3 is the better symmetry (§3.4).
2. Twisted cycles of length 4j are approximately Poisson with mean ρΔ(Δ−1)^{2j−1}/(4j) (7 groups, within 15 %),
   each removing about c_j of the words (§3.1).
3. Solutions avoid short twisted cycles: a solution keeps n* = R_j e^{−μ_A⁰λc_j} of each length. Checked on six
   anneal solutions (first session), and on 17 uniformly sampled ones (S2): mean 0.76 twisted 8-cycles against 4.2 at
   random, n* = 0.46 (§3.1).
4. S2. The price of a short-cycle-prone involution is its avoidance. One formula fits four order-2 spaces at (6,8)
   to within 0.4 nats: P(valid) ≈ P(no twisted 4- or 8-cycle)·e^{−(μ_A⁰−6)}. Doubling ρ (r = 23 instead of 11 on
   PSL(2,11)×Z24) empties the lower tail. The first session's charge for the cheap long cycles is not seen (§3.4).
5. S2. At odd D, an involution's Anti elements are missed at e^{−λ/2−π}, with π = P_ℓ|Fix(β)|/N palindromic shots on
   the Lang image and none elsewhere. Three checks within 15 % (§3.5). So conjugation-type order 2 stays dead at odd D
   (first session; 16 squad runs). A tight, balanced involution pays almost nothing for Anti.
6. S2. **At odd D, order 6 with a tight balanced involution beats order 3**, with about half the clumps in four groups:
   SL(2,64) and SL(2,8)² at (12,7), PSL(2,25)² at (14,9), SL(2,64)×Z403 at (15,9) (§5.5). The first session's
   "odd D: odd orders only" is withdrawn for k ≥ 6.
7. Even orders work at even D when every involution in ⟨α⟩ has a large centralizer. Order 6 on SL(2,64)×Z13: 3/3 seeds,
   4.7·10³–3.7·10⁴ evaluations, against 1.7·10⁵ for order 3 (§5.1). Record Δ13·D8 6,999,552 (§5.2).
8. The corrected rule (§4) ranks every k = 2 run in the squad logs correctly, and every odd-D screen of §5.5.

**Weak patterns**
1. The long-cycle factor exp(λΣR_j c_j): about right on SL(2,25) in the bulk (1.55 measured against 1.30). On
   PSL(2,11)×Z24 the symmetric best class beats random S, against the prediction (random excess ε ≈ 2.7).
2. S2 (demoted from the first session's strong item 6). The (6,8) anneal success order (Frobenius 5/6, conjugation
   2/6, r = 11 2/6, r = 23 0/6) matches the charged rule. For Frobenius against conjugation it is the reverse of the
   solution densities, and 5/6 against 2/6 is not significant (p = 0.12). It may be a landscape effect.
3. S2. At odd D the measured p1 is 1.2–1.7 times the rule's μ_A, more for lower orders (twelve screens,
   `out/rule_table2.txt`).
4. The twisted 12-cycle count is overdispersed (sd ≈ 3 × Poisson); solutions sit below its mean.
5. Free elements of Anti(α³) are missed 1.2–2.8× more often than generic ones at even D (§5.1). Unexplained.

**Dead ends (predicted and seen)**
1. Order 2 at odd D: μ/2 + √μ > μ/3 even with palindromes (§3.5). With conjugation it is far worse (all squad runs).
2. Order 2 at even D beyond (6,8): order 3 has μ/3 against μ/2 and enough room (squad rounds 2–5).
3. Order 4 near the current records: no group with clean fixed-point structure (§5.3).
4. SL(2,8)²×Z14 at (13,8): its random-symmetric minimum is twice SL(2,7)²×Z31's, and its anneals stall at 3
   uncovered orbits (§5.2).
5. S2. Product groups at (14,9): PSL(2,25)², +4.8 %, mixes poorly. The order-3 median is 4× the Poisson value and
   order 6 sits at p10 = 19 clumps (§5.5).
6. S2. An apparent law in the order-3 near misses at (6,8), "always exactly two fixed points uncovered", was an
   artefact: all 126 such samples were one class (§3.4).

**Records and runs of the second session:** RESULTS-SUMMARY.

## 6b. Next steps (for later sessions)

1. **Odd D with order 6** (S2, §5.5): (15,9) on SL(2,64)×Z403 if this session did not finish it, and (13,9) on
   SL(2,64)×Z133 (+2.9 %, μ_A 11.0, about 4·10⁴ evaluations at about 0.4 s each). Both are Frobenius type with
   a cyclic part balanced as Z_{n₁}×Z_{n₂}, α³ fixing one factor and negating the other.
2. **Order 6 at the big even-D cells**, where compute is the limit: (13,10) on SL(2,16)²×Z21 (§5.3; checkpoints in
   `runs/ckpt/an1310_*.ckpt`, resumable with CKPT=). The same swap construction gives candidates at (14,10)
   (SL(2,16)²×Z42, Δ = 6+6+2 with OSUB=2).
3. **(15,8) with mixed orbits** (6+6+3) on SL(2,8)²×Z37: checkpoints `runs/ckpt/an158_*.ckpt`.
4. **The low-μ odd-D records** (S2 observation): (11,9), (12,9), (14,9) and (16,9) sit at μ = 14–16, against
   μ ≈ 30–50 where order-3 searches still solve elsewhere. Order 3 alone should push them by several per cent where
   suitable group orders exist (§5.5 lists the order-6 options).
5. **Small-N cells:** before trusting the rule, count the space (checklist §4.1 item 7). The census tools are
   `classes68.py` and `NEARDUMP`.
6. Open questions:
   - why the annealer finds the isolated Frobenius class at (6,8) more often than the ~50 conjugation classes (§5.4);
   - the 6-nat offset of the Poisson baseline at the extreme tail (§3.4): a model of the heterogeneity across S;
   - PSL(2,11)×Z24's random sets lose far more words than Poisson (ε ≈ 2.7), while its symmetric sets do not (§3.1);
   - free elements of Anti(α³) are missed 1.2–2.8× more often at even D (§5.1).

No haiku-squad round was run in either session. Both were analysis plus long, CPU-bound anneals on a shared 4-core
box, where more hands add no compute. The candidate lists came out of the rule itself, a handful of groups each.

## 7. Files (`research/theorems/order2/`)

- `hgroups.py`: SL/PSL(2,q) (q a prime power, haar_gen3's field encoding) × Z_n and products, as numpy permutation
  arrays; reads haar_gen3 solution files.
- `twist.py`: twisted and involutive coincidence census, cost, ball sizes, shot counts.
  - `twist.py sol FILE --alpha mat(..) --r R`: census of a solution file (it recovers the symmetric frame).
  - `twist.py randorb …`: random β-invariant S.
  - `twist.py randsample …`: random S.
- `analyze_census.py`: cost by (n₄, n₈) class and the log-linear fit → `out/analyze_6_8.txt`.
- `levels_by_class.py`: ball sizes and median cost by class against random S → `out/levels_by_class_*.txt`.
- `targets.py`, `show_targets.py`: uncovered elements by type (Fix, Anti, involutions, other), binned by generic
  rate → `out/targets/*.json`.
- `rule.py`: the corrected rule as a calculator, with 24 worked cases → `out/rule_table.txt`.
- `src/haar_order2.c`: research/squads/table_squad/src/haar_inv.c plus five modes (header comment):
  - AFSWAP, ASWAPC: the swap automorphisms of G×G;
  - OSUB: one orbit of size s < k;
  - CLASSES: miss rate per stabiliser class, with RANDORB;
  - BESTOUT: the best S of an unsolved run.
  Build: `gcc -O3 -march=native -fopenmp -o haar_order2 haar_order2.c -lm`.
- `classes.py`: summary of CLASSES output → `out/classes/summary.txt`.
- `check_np.py`: third independent diameter check (own group code, numpy, up to about 10⁷ vertices).
- `check_lowmem.c`: fourth, low-memory checker in C (own GF(p^k) and SL(2,q) arithmetic, products, Z_n; bitset BFS
  from (e,A) and (e,B), N/2 bytes). Validated VALID on the (13,8) record and INVALID (ecc 9) on a near miss. Build:
  `gcc -O3 -march=native -fopenmp -o check_lowmem check_lowmem.c`.
- `uncovered.py`: lists the uncovered α-orbits of a near-solution (swap-conjugation groups).
- S2: `classes68.py` (stabiliser in Fix², class invariant from trace multisets; distinct classes among solution files),
  `symmetry68.py` (the full symmetry group of S ⊂ SL(2,q) by linear algebra over GF(q); `--to FILE2` lists the maps
  T with T(S) = S₂), `classsize68.py` (class size in the symmetric space, by brute force).
- S2: `rule.py --second` (odd-D cases with the palindrome term → `out/rule_table2.txt`).
- S2: `src/haar_order2.c` mode `NEARDUMP=c` (with RANDORB): prints S and the uncovered elements of every sample of
  cost ≤ c, including solutions.
- S2: `runs/r2/` (this session's logs, launch scripts, near-miss dumps, screens), `runs/ckpt/` (anneal checkpoints),
  `out/classes68/` (class censuses, explicit maps, brute-force class sizes), `sols/d68/` (adds the uniform-sample
  solutions).
- `runs/`: haar logs of this session (anneals `an138_*`, random symmetric screens `ro*`).
- `sols/`: the two (6,8) records (copied from the table-squad branch) and the order-6 (13,8) solutions.
- `out/`: census samples (`*.jsonl.gz`: one JSON line per S with its cost, ball sizes, census and S), tables.

Commands used:
```
python3 twist.py randorb psl 11 24 --d 6 --D 8 --m 3 --f 0 --alpha "mat(5,1,7,6)" --samples 4000 --seed 1 --out out/ro_psl11_24_r11.jsonl
python3 twist.py randorb psl 11 24 --d 6 --D 8 --m 3 --f 0 --alpha "mat(5,1,7,6)" --r 23 --samples 4000 --seed 2 --out out/ro_psl11_24_r23.jsonl
python3 twist.py randorb sl 25 --d 6 --D 8 --m 3 --f 0 --alpha "mat(5,21,12,20)" --samples 4000 --seed 3 --out out/ro_sl25.jsonl
python3 twist.py randsample psl 11 24 --d 6 --D 8 --samples 4000 --seed 4 --out out/rs_psl11_24.jsonl
python3 twist.py randsample sl 25 --d 6 --D 8 --samples 4000 --seed 5 --out out/rs_sl25.jsonl
python3 twist.py sol sols/d6D8_psl_11_24_orb2f0_s1.txt --alpha "mat(5,1,7,6)" --r 11
python3 twist.py sol sols/d6D8_sl_25_1_orb2f0_s1.txt --alpha "mat(5,21,12,20)" --r 0
for q in 13 17 19 23 27 29 31; do python3 twist.py randorb sl $q --d 6 --D 6 --m 3 --f 0 --samples 300 --seed $q --maxlen 6 --out out/rj/sl$q.jsonl; done
python3 targets.py sl 25 4 --d 6 --D 9 --m 3 --f 0 --frob 1 --r 3 --samples 200 --json out/targets/d6D9_sl25x4_k2frob.json   (and --r 3 without --frob for conjugation)
python3 targets.py sl 25 --d 6 --D 8 --m 3 --f 0 [--frob 1] --samples 600 --json out/targets/d6D8_sl25_k2{conj,frob}.json
python3 targets.py psl 11 24 --d 6 --D 8 --m 3 --f 0 --alpha "mat(5,1,7,6)" --r 11 --samples 600 --json out/targets/d6D8_psl11x24_k2conj.json
ORBIT="6 2 1" AFROB=1 AR=4 haar_inv 13 8 600 SEED 8 OUT.txt sl 64 13                       (seeds 1-3)
ORBIT="6 2 1" ASWAPC=1 AR=6 haar_order2 13 8 300 SEED 8 OUT.txt prod sl 7 sl 7 31           (seeds 1-14)
ORBIT="6 2 1" AFSWAP=1 AR=3 haar_order2 13 8 900 SEED 8 OUT.txt prod sl 8 sl 8 14           (and AR=5, AFSWAP=2)
```
