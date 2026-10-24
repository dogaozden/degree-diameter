# ORDER2: why an order-2 symmetry won at (6,8), and where even orders win

Job "thm-order2", 2026-10-24, one Opus cloud session (4 cores). Branch `claude/thm-order2-symmetry-gap-4e2nmi`.
Scripts, logs and saved outputs are in `order2/` (list in §7). Builds on `research/theory/BEYOND_RANDOM.md`
(branch `claude/cd-theory-beyond-random-3ybyf2`) and on the table-squad log (`research/squads/LOG.md`, branch
`claude/degree-diameter-table-squad-0xgp3g`).

Notation as in BEYOND_RANDOM: G of order N, S of size Δ, H(G,S) with edges (g,A) ~ (sg,B), ℓ = D − 1, W the number
of binding words, λ = W/N, μ = N e^{−λ} (haar_sym's μ). α is an automorphism with α(S) = S, k its order, μ_A the
clumped Poisson mean (BEYOND_RANDOM formula (1)). For an involution β: σ is the letter permutation it induces on S,
ι is inversion, β* = ι∘β (an anti-automorphism), Anti(β) = Fix(β*) = {u : β(u) = u⁻¹}, and ρ = |Anti(β)|/N.
"Evaluations" are haar_sym cost evaluations, the unit of the effort law evals ≈ 10⁵·e^{(μ_A − 13)/2}.

## Short answer

1. **The gap is "self-averaging".** BEYOND_RANDOM §4.2 computed the mean word loss of an involution,
   δ ≈ ρℓ²/8 with ρ ≥ 1/|Fix(β)|. For both (6,8) winners (ρ ≈ 1/24, ℓ = 7) that is about 25 % of the binding words,
   which would be fatal. The mean is right. What fails is the next step: "each even subword is an essentially fresh
   random element, so the loss is self-averaging". Each coincidence is one *twisted cycle* v·σ(v) of the graph, and
   the same cycle acts at every position of every word. So the loss is carried by a few Poisson-distributed cycles,
   and the short ones carry most of it:
   - twisted 4-cycles: mean 0.16–0.5 per random symmetric S at (6,8). Each one multiplies the cost about 2–4 times
     (measured);
   - twisted 8-cycles: mean about 4. Each multiplies the cost by e^{0.10–0.16} (fitted; predicted e^{0.13});
   - twisted 12-cycles: mean 65–80, each nearly free (0.06 % of the words).

   4-cycles carry half the mean loss and 8-cycles a third. A search simply avoids both. **Both (6,8) record sets have
   no twisted 4-cycle and no twisted 8-cycle**, a class that holds about 4 % of random symmetric S (§3.1).
2. **Even D matters.** At odd D each side's word set is also inverse-closed. Then β* is a symmetry of it, and every
   element of Anti(β), at least N/|Fix(β)| of them, becomes an extra fixed target missed with probability ≈ e^{−λ/2}.
   No choice of S avoids this. At even D the term is absent. Measured: elements of Anti(β) are missed at the generic
   rate at even D (ratio 1.00–1.10) and 2–27 times more often at odd D (§3.2). That is why every k = 2 run at odd D
   failed: squad rounds 1–2 at D = 5, (6,7), (6,9), (7,9) and (8,7).
3. **Small Δ matters twice.** With Δ = 6, order 3 leaves only two orbits. Its orbit space at N ≈ 15,840 has about
   e^{16} sets, which is at its first-moment ceiling. Order 2 gives three orbits, about e^{25} sets. Small Δ also keeps the
   twisted 8-cycles few enough to avoid: their mean is ρΔ(Δ−1)³/8.
4. **The fixed points are not the issue** at D = 8: 24 fixed points cost 24·e^{−λ/2} ≈ 1.1 missed elements.
5. **Corrected rule** (§4). An involution β in ⟨α⟩ costs nothing beyond its fixed points at even D, as long as its
   short twisted cycles are rare: Poisson means R_j = ρΔ(Δ−1)^{2j−1}/(4j) of order a few or less. It then pays only
   for its long twisted cycles, a factor ≈ exp(λ Σ_{j > j*} R_j c_j) on μ_A, with
   c_j = 2j(ℓ−2j+1)/(Δ(Δ−1)^{2j−1}). At odd D it also pays (|Fix(β)| + |Anti(β)|)(2/k) e^{−λ/2}. That is at least
   2√μ for k = 2 (AM–GM with |Fix|·|Anti| ≥ N), and in practice much more.
6. **Prediction tested: even orders win at even D when every involution in ⟨α⟩ has a large centralizer.** Order 6
   (the Frobenius x ↦ x² of GF(64), whose cube x ↦ x⁸ is an involution fixing SL(2,8)) on the (13,8) record group
   SL(2,64)×Z13:
   - 3 of 3 seeds solved, in 4,665, 9,625 and 37,185 evaluations;
   - order 3 needed 170,313 evaluations (one seed, BEYOND_RANDOM);
   - the rule predicted ≈ 10⁴ and 1.1·10⁵ (§5.1).

   The old rule ("odd k is required") would have excluded order 6.

   **New record Δ13·D8 = 6,999,552 vertices** (was 6,814,080, +2.7 %). Order 6 on SL(2,7)²×Z31, with
   α(x₁, x₂, z) = (c x₂ c⁻¹, x₁, 6z) and c of order 3, ORBIT="6 2 1". Three independent checks passed: haar_sym's full
   check, `research/frontier/build_haar2.py` (VALID, edge sha256 daf0ccf9…), and this job's `order2/check_np.py`
   (VALID) (§5.2).
7. **Where else order 2 should win:** by the rule, nowhere else in the current table. It needs D even, an order-3
   space with only two orbits, and few twisted 8-cycles; (6,8) is the only such cell. Even orders above 2 need
   Frobenius-type groups, which exist near the records only at (13,8) (§5.3).

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

### 3.3 Which assumption failed, in the brief's terms

| suspected assumption | verdict |
|---|---|
| the involution's fixed points | not the problem: \|Fix\|·e^{−λ/2} ≈ 1.1 at (6,8). Fixed points are paired as predicted (Fix/√p ≈ 0.8–1.06) |
| the Anti set | its size is right (tight uncertainty bound), but it enters twice. **At even D it matters only through twisted cycles, which are rare and avoidable when short. At odd D it is a set of unavoidable extra targets.** The old argument merged the two and treated the first as self-averaging |
| small Δ | yes, twice: k = 3 has only two orbits at Δ = 6 (orbit space ≈ e^{16} at N ≈ 15,840), and the twisted 8-cycle mean ρΔ(Δ−1)³/8 ≈ 4 is small enough to avoid |
| even D | yes: it removes the Anti-target term entirely |

The same error decided BEYOND_RANDOM's ranking of **Z6** (§4.2 there): "(Frobenius of order 2) × (conjugation of
order 3) … inherits the σ reflections, at rate about 1/q₀² … ranks it below plain k = 3".
- Its reflection penalty is the involution's twisted cycles again, treated as self-averaging. For a Frobenius
  involution ρ ≈ 1/q₀³, and they are cheap (§5.1).
- The other relation it cites, "x commutes with σ(x)", is a 6-cycle through the fixed letter e. Such a 6-cycle is rare
  and disappears with f = 0 or the OSUB layout.
- The order-6 Frobenius x ↦ x² of GF(64) is exactly such a Z6: its square has order 3 (x ↦ x⁴) and its cube is the
  Frobenius involution x ↦ x⁸. It beat order 3 by 5–35× in evaluations on the same group (§5.1).

## 4. The corrected rule

For α of order k with α(S) = S, f fixed generators and m orbits of size k:

    μ_A ≈ [ μ/k  +  Σ_{1 ≠ H ≤ ⟨α⟩} #{x : Stab(x) = H}·(|H|/k)·e^{−λ/|H|}
              +  [D odd]·Σ_{involutions β ∈ ⟨α⟩} (2/k)·|Anti(β) \ Fix(β)|·e^{−λ/2} ]
          × exp( λ · Σ_{β} Σ_{j : R_j(β) > R*} R_j(β)·c_j )

with R_j(β) = ρ_β Δ(Δ−1)^{2j−1}/(4j), c_j = 2j(ℓ−2j+1)/(Δ(Δ−1)^{2j−1}) and R* ≈ 5. Families with R_j ≤ R* are
avoided by the search at no measurable cost. Plug μ_A into the effort law. `order2/rule.py` implements this and prints
the 24 worked cases of `out/rule_table.txt`, each with its observed outcome.

The principled form of the twisted-cycle term is the generating-function charge Σ_j R_j(1 − e^{−μ_A⁰λc_j}) nats,
with n* = R_j e^{−μ_A⁰λc_j} cycles left in a solution (§3.1). rule.py prints both forms. The n* half is confirmed on
all six solutions. The nats half is not: in effort terms it over-predicts the two (6,8) solves (last item below).

In words:

1. Clumps of size k divide μ by k (BEYOND_RANDOM).
2. Each subgroup H of ⟨α⟩ pays for its fixed points at rate e^{−λ/|H|}. This is bounded for Frobenius-type α on
   SL(2,p^e) for every e, and for k = 2, 3 conjugation in SL(2,q).
3. **Odd D:** every involution in ⟨α⟩ also pays for its Anti set. For k = 2 the Fix and Anti terms together are at
   least (|Fix| + |Anti|)e^{−λ/2} ≥ 2√μ (by 2.4), reached only by a balanced involution. For conjugation-type
   involutions it is far more and kills the method. With k = 3 available, no even order should be used at odd D.
4. **Even D:** an involution's twisted cycles are a Poisson field with means R_j ∝ ρ(Δ−1)^{2j}. The short families
   are avoided when R_j ≲ 5. The long ones cost e^{λ R_j c_j} each. They are negligible when ρ is tiny (Frobenius
   involutions, ρ ≈ 1/|SL(2,p^{e/2})|) and about 1.3 at (6,8) with ρ = 1/24.
5. A symmetry is worth using when the resulting μ_A, and the orbit space ln #S ≈ m ln(N/k) − ln m!, beat the
   alternatives.

How well it predicts (`out/rule_table.txt`):
- Every odd-D k = 2 failure in the squad logs gets μ_A ≫ μ (96–136 against μ = 25–67).
- Every even-D k = 2 failure outside (6,8) gets μ_A 1.8–3.2 times the order-3 value at the same cell and order:
  (6,10), (7,8), (8,8), (9,8).
- The order-6 runs at (13,8) are predicted to within their scatter.
- At (6,8) the rule over-predicts the effort of the two solves. With the 12-cycle penalty it predicts
  1.4·10⁷ and 4.7·10⁶ evaluations, against 3.3·10⁵ and 2.1·10⁶. Without the penalty it predicts 1.0·10⁶ and
  4.4·10⁵. So the long-cycle term is real on SL(2,25) (§3.1) but too small to see in two runs.

### 4.1 Choosing a symmetry: a checklist for future searches

1. **Odd D:** use odd k only (3, or 5 with small fixed sets). Any involution in ⟨α⟩ brings ≥ N/|Fix| Anti targets
   at rate e^{−λ/2}.
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
7. **Screen before annealing:** RANDORB's lower tail in clump units (cost/k) ranks candidates the way the anneals
   did. On the solved groups, p10 was 6 clumps (SL(2,64)×Z13, about 10⁴ evaluations) and 10.7 (SL(2,7)²×Z31, about
   1.3·10⁵).

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
| SL(2,8)²×Z14 | 3,556,224 (+4.4 %) | swap∘Frobenius, z ↦ 3z or 5z | 59.9 | 15.0 | 60–72, 97–104 | 4 seeds: best 18–26 (one orbit = 6) |
| SL(2,64)×Z14 | 3,669,120 (+7.7 %) | Frobenius order 6, z ↦ 3z | 86.7 | 20.9 | 70, 130 | not run (≈ 5·10⁶ evaluations by the rule) |
| PSL(2,13)²×Z3 | 3,577,392 (+5.0 %) | swap∘conj(order 3), z ↦ 2z | 64.3 | 14.7 | 52, 91 | RESULT-PSL13 |
| PSL(2,7)²×Z126 | 3,556,224 (+4.4 %) | swap∘conj(order 3), z ↦ 5z | 59.9 | 11.5* | 57, 132 | screen only: no order-6 multiplier of Z9 moves Z3, and the large cyclic factor mixes badly |
| SL(2,5)²×Z247 | 3,556,800 (+4.4 %) | swap∘conj(order 3), z ↦ 69z | 60.0 | ≈ 11* | 108, 364 | screen only: the large cyclic factor mixes badly |

\* The rule's μ_A counts only clumps, fixed points and twisted cycles. It does not see the poor mixing of a large
cyclic factor with a small simple group (STRUCTURE §5). The random-symmetric screen does, and it is the better guide
there.

**The record graph.** `sols/d13D8_prod_sl_7_sl_7_31_orb6swc_s2.txt`, also in `research/frontier/sols/`:
- S = {e} ∪ O₁ ∪ O₂ in SL(2,7) × SL(2,7) × Z31, with O_i = {s_i, α(s_i), …, α⁵(s_i)};
- c = mat(2,0,4,4), of trace −1 and order 3;
- 3,499,776 group elements, so 6,999,552 vertices.

The three checks:
- haar_order2's full diameter check (all four side pairs within 8): OK.
- `research/frontier/build_haar2.py`, which rebuilds the group from its definition: ecc 8 from both sides, nothing
  unreached, 45,497,088 edges, every degree 13, no repeated edge, edge-list sha256
  daf0ccf91e35dc587d6bed076ba05be225de3cd0aa2c4607032cffe86af6ebb2. VALID
  (`checks/d13D8_prod_sl_7_sl_7_31_orb6swc_s2.check.txt`).
- `check_np.py`, a third group implementation: BFS from (e,A) and (e,B) over all 6,999,552 vertices, ecc 8 from both,
  nothing unreached, 13 distinct generators. VALID (`checks/…check_np.txt`).

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

### 5.3 Where else order 2, or another even order, should win

By the rule, an even order beats order 3 only if both of these hold:
- D is even;
- either the order-3 orbit space is starved (two orbits at small N) and the involution's 8-cycles are avoidable
  (R₂ = ρΔ(Δ−1)³/8 ≲ 5, i.e. |Fix(β)| ≳ 20, 40, 70 for Δ = 6, 7, 8), or the even order is larger than 3 with
  bounded fixed-point costs (Frobenius type).

Going through the table:
- **Order 2:** only (6,8). At (6,10), (7,8), (8,8) and (9,8) order 3 has room. There μ/2 against μ/3 is 2–8 nats of
  μ_A, which matches the squad's failures (`out/rule_table.txt`). At odd D: never (§3.2).
- **Order 4:** needs a Frobenius of order 4 (SL(2,16), SL(2,81)) or conjugation by an element whose square has a
  large centralizer. Near the records, the cyclic factors either have no automorphism of order 4 (primes ≡ 3 mod 4)
  or leave α² trivial on them, which puts thousands of elements in Fix(α²). Checked by hand: (8,8), (9,8), (8,10),
  (9,10), (10,10), (13,8). The only clean one is (10,10) on SL(2,81)×Z58, and there μ_A ≈ 7.6 equals order 3's. No
  gain predicted.
- **Order 6:** needs Δ ≥ 12 for two orbits. Of those cells, (12,8), (14,8) and (16,8) are above the first-moment
  ceiling even with μ/6, and the D = 10 cells need groups of order ≥ 10⁸ with a Frobenius of order 6 near the
  records (SL(2,729) is 16 % too big for (13,10)). That leaves (13,8), §5.2.
- **Order 8 and up:** needs Δ ≥ 16 for two orbits; no candidate group.
- **(13,10) on SL(2,16)²×Z21**, with α = swap∘conj(order 3) × (z ↦ 5z), r of order 6 (Z21 = Z3 × Z7). The
  random symmetric screen (16 samples, `runs/ro1310_sl16sq_21_k6.txt`) gives min 23 and p10 26 at μ = 35.5. That is
  4.3 clumps, better than SL(2,64)×Z13 (6.2), which solved in about 10⁴ evaluations. Anneal (2 threads, 0.57 s per
  evaluation, 4-hour budget): RESULT-1310.
  - N = 349,574,400, so 699,148,800 vertices, +4.7 % over our 667,903,200.
  - μ = 36.4. The rule gives μ_A ≈ 9.1 for order 6 (fixed points 3.0) against ≈ 13 for order 3 at the same N, which is
    about 7× fewer evaluations.
  - The effort law predicts about 1.4·10⁴ evaluations. At about 1.2 s each (the (13,10) record run took 1.1 s per
    evaluation at N = 3.3·10⁸) that is 5–20 hours on one core, beyond this session.

## 6. Ranked conclusions

**Proved**
1. Reflection lemma: an involutive symmetry's coincidences are exactly the twisted cycles v·σ(v), v ∈ Anti(β) (§2.1).
   Their expected number per length is ρ × (number of words) up to the words without a singleton orbit (§2.6).
2. |Fix(β)|·|Anti(β)| ≥ N, tight for trace-0 conjugation in SL(2,q) and for Frobenius of order 2 on SL(2,q₀²);
   z ↦ −z on Z_n with n even is not tight (§2.2).
3. At odd D, β* = inversion∘β is a symmetry of each side's binding multiset, so Anti(β) consists of β*-fixed targets.
   At even D it is not a symmetry (§2.3).
4. |Fix| + |Anti| ≥ 2√N (§2.4).

**Conjectured with strong evidence**
1. Twisted cycles of length 4j are approximately Poisson with mean ρΔ(Δ−1)^{2j−1}/(4j) (7 groups, within 15 %),
   each removing about c_j of the words (8-cycles: fitted 0.10–0.16 per cycle in ln cost, predicted 0.13) (§3.1).
2. The search avoids the short twisted cycles. Both (6,8) record sets have none, against 4 % of random symmetric S.
   Quantitatively, a solution keeps n* = R_j e^{−μ_A⁰λc_j} cycles of each length. This parameter-free prediction
   matches all six solutions in hand, at Δ = 6 and Δ = 13 (§3.1).
3. At odd D an involution's Anti elements are missed at about √p, and its unavoidable cost kills conjugation-type
   order 2. At even D they are ordinary targets (§3.2). Squads: none of the 16 order-2 runs at odd D solved. Their best
   values were 6–107 uncovered (6 at (9,5), where order 3 solves SL(2,11) in 0.1 s).
4. Even orders work at even D when every involution in ⟨α⟩ has a large centralizer. Order 6 on SL(2,64)×Z13: 3/3 seeds,
   4.7·10³–3.7·10⁴ evaluations, against 1.7·10⁵ for order 3 (§5.1).
5. The corrected rule (§4) ranks every k = 2 run in the squad logs correctly.

**Weak patterns**
1. The long-cycle factor exp(λΣR_j c_j): about right on SL(2,25) (1.55 measured against 1.30). On PSL(2,11)×Z24 the
   symmetric best class beats random S, against the prediction. Its random baseline has an unusual excess (ε ≈ 2.7).
2. The effort of the (6,8) solves (two runs) is better than the rule's penalised prediction by 2–40×.
3. σ-palindromic words reduce the Anti penalty at odd D, more for Frobenius than for conjugation (§3.2).
4. The twisted 12-cycle count is overdispersed (sd ≈ 3 × Poisson), and the record sets sit about 1 sd below its mean.

**Dead ends (predicted and seen)**
1. Order 2 at odd D with conjugation (all squad runs; `rule_table.txt`). With Frobenius it is better but still worse
   than random S on SL(2,25)×Z4 at (6,9), because Z4 doubles Anti.
2. Order 2 at even D beyond (6,8): order 3 has μ/3 against μ/2 (squad rounds 2–5).
3. Order 4 near the current records: no group with clean fixed-point structure (§5.3).
4. SL(2,8)²×Z14 at (13,8): its random-symmetric minimum is twice SL(2,7)²×Z31's, and its anneals stall at 3
   uncovered orbits (§5.2).

## 6b. Next steps (for later sessions)

1. **Order 6 at the big even-D cells**, where compute is the limit. (13,10) on SL(2,16)²×Z21 (§5.3) screens better
   than the group that solved (13,8) in 10⁴ evaluations. The same swap construction gives candidates at (14,10)
   (SL(2,16)²×Z42, Δ = 6+6+2 with OSUB=2).
2. **(13,8) next rungs:** PSL(2,13)²×Z3 (3,577,392; best 8 in 30 min) and SL(2,8)²×Z14 (3,556,224; best 18). Try
   more seeds, and OSTAB=1 (the energy counts uncovered orbits; it matters when the last uncovered elements have
   nontrivial stabilisers).
3. **(15,8) with mixed orbits** (6+6+3) on SL(2,8)²×Z37, §5.2b, if this session's seeds did not finish it.
4. Two unexplained patterns worth a look:
   - PSL(2,11)×Z24's random sets lose far more words than Poisson (ε ≈ 2.7) while its symmetric sets do not (§3.1);
   - free elements of Anti(α³) are missed 1.2–2.8× more often at even D (§5.1).

No haiku-squad round was run in this session. The work was analysis plus long, CPU-bound anneals on the shared
4-core box, where more hands add no compute, and the candidate lists came out of the rule itself. Each was a handful
of groups.

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
