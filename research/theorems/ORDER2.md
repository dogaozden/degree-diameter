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

   The old rule ("odd k is required") would have excluded order 6. Record attempts with order 6 above 3,407,040 are
   in §5.2.
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
| the involution's fixed points | not the problem: |Fix| e^{−λ/2} ≈ 1.1 at (6,8). Fixed points are paired as predicted (Fix/√p ≈ 0.8–1.06) |
| the Anti set | its size is right (tight uncertainty bound), but it enters twice. **At even D it matters only through twisted cycles, which are rare and avoidable when short. At odd D it is a set of unavoidable extra targets.** The old argument merged the two and treated the first as self-averaging |
| small Δ | yes, twice: k = 3 has only two orbits at Δ = 6 (orbit space ≈ e^{16} at N ≈ 15,840), and the twisted 8-cycle mean ρΔ(Δ−1)³/8 ≈ 4 is small enough to avoid |
| even D | yes: it removes the Anti-target term entirely |

## 4. The corrected rule

For α of order k with α(S) = S, f fixed generators and m orbits of size k:

    μ_A ≈ [ μ/k  +  Σ_{1 ≠ H ≤ ⟨α⟩} #{x : Stab(x) = H}·(|H|/k)·e^{−λ/|H|}
              +  [D odd]·Σ_{involutions β ∈ ⟨α⟩} (2/k)·|Anti(β) \ Fix(β)|·e^{−λ/2} ]
          × exp( λ · Σ_{β} Σ_{j : R_j(β) > R*} R_j(β)·c_j )

with R_j(β) = ρ_β Δ(Δ−1)^{2j−1}/(4j), c_j = 2j(ℓ−2j+1)/(Δ(Δ−1)^{2j−1}) and R* ≈ 5. Families with R_j ≤ R* are
avoided by the search at no measurable cost. Plug μ_A into the effort law. `order2/rule.py` implements this and prints
the 24 worked cases of `out/rule_table.txt`, each with its observed outcome. In words:

1. Clumps of size k divide μ by k (BEYOND_RANDOM).
2. Each subgroup H of ⟨α⟩ pays for its fixed points at rate e^{−λ/|H|}. This is bounded for Frobenius-type α on
   SL(2,p^e) for every e, and for k = 2, 3 conjugation in SL(2,q).
3. **Odd D:** every involution in ⟨α⟩ also pays for its Anti set. By 2.4 that is at least 2√μ·(2/k)·(1/2)·2 for a
   balanced involution. For conjugation-type involutions it is far more and kills the method. With k = 3 available,
   no even order should be used at odd D.
4. **Even D:** an involution's twisted cycles are a Poisson field with means R_j ∝ ρ(Δ−1)^{2j}. The short families
   are avoided when R_j ≲ 5. The long ones cost e^{λ R_j c_j} each. They are negligible when ρ is tiny (Frobenius
   involutions, ρ ≈ 1/|SL(2,p^{e/2})|) and about 1.3 at (6,8) with ρ = 1/24.
5. A symmetry is worth using when the resulting μ_A, and the orbit space ln #S ≈ m ln(N/k) − ln m!, beat the
   alternatives.

How well it predicts (`out/rule_table.txt`):
- Every odd-D k = 2 failure in the squad logs gets μ_A ≫ μ (96–136 against μ = 25–67).
- Every even-D k = 2 failure outside (6,8) gets μ_A 1.8–2.4 times the order-3 value at the same cell: (6,10), (7,8),
  (8,8), (9,8).
- The order-6 runs at (13,8) are predicted to within their scatter.
- At (6,8) the rule over-predicts the effort of the two solves. With the 12-cycle penalty it predicts
  1.4·10⁷ and 4.7·10⁶ evaluations, against 3.3·10⁵ and 2.1·10⁶. Without the penalty it predicts 1.0·10⁶ and
  4.4·10⁵. So the long-cycle term is real on SL(2,25) (§3.1) but too small to see in two runs.

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
the record's order, so they are not records.

### 5.2 Record attempts at (13,8) with order 6 (current record 6,814,080 = 2 × 3,407,040)

New automorphisms in `order2/src/haar_order2.c` (haar_inv plus two modes):
- AFSWAP=j: (x₁, x₂) ↦ (F^j(x₂), x₁) on G×G.
- ASWAPC=1: (x₁, x₂) ↦ (c x₂ c⁻¹, x₁).
Both have order 2·ord(F^j) or 2·ord(conj c). The involution α³ fixes a diagonal copy of G, so ρ ≈ 1/|G|.

| group | N (vs record) | α | μ | μ_A (rule) | random symmetric: min, p10 | anneals |
|---|---|---|---|---|---|---|
| SL(2,7)²×Z31 | 3,499,776 (+2.7 %) | swap∘conj(order 3), z ↦ 6z | 49.4 | 11.0 | 35, 64 | RESULT-SL7 |
| SL(2,8)²×Z14 | 3,556,224 (+4.4 %) | swap∘Frobenius, z ↦ 3z or 5z | 59.9 | 15.0 | 60–72, 97–104 | 4 seeds: best 18–26 (one orbit = 6) |
| SL(2,64)×Z14 | 3,669,120 (+7.7 %) | Frobenius order 6, z ↦ 3z | 86.7 | 20.9 | 70, 130 | not run (≈ 5·10⁶ evaluations by the rule) |

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

## 6. Ranked conclusions

**Proved**
1. Reflection lemma: an involutive symmetry's coincidences are exactly the twisted cycles v·σ(v), v ∈ Anti(β) (§2.1).
2. |Fix(β)|·|Anti(β)| ≥ N, tight for trace-0 conjugation in SL(2,q) and for Frobenius of order 2 on SL(2,q₀²);
   z ↦ −z on Z_n with n even is not tight (§2.2).
3. At odd D, β* = inversion∘β is a symmetry of each side's binding multiset, so Anti(β) consists of β*-fixed targets.
   At even D it is not a symmetry (§2.3).
4. |Fix| + |Anti| ≥ 2√N (§2.4).

**Conjectured with strong evidence**
1. Twisted cycles of length 4j are approximately Poisson with mean ρΔ(Δ−1)^{2j−1}/(4j) (7 groups, within 15 %),
   each removing about c_j of the words (8-cycles: fitted 0.10–0.16 per cycle in ln cost, predicted 0.13) (§3.1).
2. The search avoids the short twisted cycles. Both (6,8) record sets have none, against 4 % of random symmetric S
   (§3.1).
3. At odd D an involution's Anti elements are missed at about √p, and its unavoidable cost kills conjugation-type
   order 2. At even D they are ordinary targets (§3.2; squad: 0 of 31 odd-D k = 2 runs reached even 10 uncovered).
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
- `src/haar_order2.c`: research/squads/table_squad/src/haar_inv.c plus AFSWAP and ASWAPC (header comment). Build:
  `gcc -O3 -march=native -fopenmp -o haar_order2 haar_order2.c -lm`.
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
