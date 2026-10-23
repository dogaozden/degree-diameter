# Structured generator sets for Haar graphs: what changes the exponent, and what does not

structured-search job (Opus), 2026-10-23, cloud container (4 cores, Xeon 2.8 GHz). Programs: `haar_sym.c`
(search), `tools/orb_screen.py` (screening), `tools/orbq.sh` (job queue). Notation follows `../frontier/SIZE_LAW.md`:
N = |G|, W = W(Δ,D) the number of binding words, λ = W/N, μ = N e^(−λ) the Poisson mean of the uncovered count.

<!-- RESULTS-SUMMARY -->

## 1. The idea: make S invariant under an automorphism

Let α ∈ Aut(G) have prime order k, and let

  S = F ∪ O_1 ∪ … ∪ O_m,  F ⊆ Fix(α) with e ∈ F, |F| = f,  O_j = {x_j, α x_j, …, α^(k−1) x_j},  Δ = f + k·m.

Then α(S) = S, so α is an automorphism of H(G,S) fixing (e,A) and (e,B). The ball of radius D−1 is α-invariant,
so the uncovered set is a union of α-orbits. Count with the Poisson model of SIZE_LAW §2.2:

- **Free orbits** (size k). The binding words fall into α-orbits of k words (α permutes the letters). A free
  element-orbit is missed with probability e^(−λ) (as for random S), and there are about N/k such orbits. The number
  of missed orbits is therefore about Poisson(μ/k): the same μ elements, but in clumps of k.
- **Fixed points** x ∈ Fix(α). Words hitting x come in α-orbits of k words that all hit x, so the number of
  word-orbits hitting x is about Poisson(λ/k). The miss probability is e^(−λ/k), much larger than e^(−λ).
- **Effective mean**: μ_eff = μ/k + |Fix(α)| e^(−λ/k) (doubled for odd D, which has two conditions).

A random S covers everything with probability ≈ e^(−εμ) (ε ≈ 1.3–2, SIZE_LAW §2.3.2). A random symmetric S
covers everything with probability ≈ e^(−ε μ_eff). With k = 3 and |Fix| ~ q (a torus), μ_eff ≈ μ/3 + small, so
**the exponent of the success probability is divided by about 3**.

What does *not* change is the first-moment ceiling. There are about N^m symmetric sets against N^(Δ−1) unrestricted
ones. Setting E[#valid S] ≈ N^m e^(−ε μ/k) = 1 gives μ ≈ k m ln N/ε = (Δ − f) ln N/ε, the same ceiling as random S
(SIZE_LAW §1.4: μ_h = Δ ln N). So orbit-symmetric S makes the band between today's wall (μ ≈ 10–25) and the
ceiling (μ ≈ Δ ln N ≈ 70–200) searchable. It cannot go above the ceiling.

## 2. Which α work (and why the others fail)

Measured with `RANDORB` (cost of random symmetric S) and `LEVELS` (ball growth); details in §5.

1. **k must be odd.** If α is an involution, two different length-2 words coincide whenever α(u) = u⁻¹ for a product
   u of generators: x_a⁻¹ α(x_b) = x_b⁻¹ α(x_a) ⇔ α(x_a x_b⁻¹) = (x_a x_b⁻¹)⁻¹, and α(x)⁻¹ = x whenever α(x) = x⁻¹.
   For α = conjugation by g (g² central) in SL(2,q) × Z_n with z ↦ −z, the set {u : α(u) = u⁻¹} = {u : (ug)² = g²}
   has density ≈ 1/q (ug of trace 0), and the z-part is automatically inverted. So a fraction ≈ 1/q of the words
   collide at *every* level. Brute force on SL(2,13) × Z_19 (300 random symmetric S) found exactly these coincidences
   at the predicted rate (9–12 %). Result: median random cost 458 against μ = 12.7 (random S: 31). For odd k,
   α(u) = u⁻¹ forces α²(u) = u, hence α(u) = u and u² = e, which is rare.
2. **α must move every small quotient.** The orbit {x, αx, α²x} has a single image in any quotient on which α acts
   trivially. Examples:
   - α trivial on the Q-part (z ↦ rz only): the matrix parts of S repeat. Costs 10⁴–3·10⁴ against μ = 13.
   - Metacyclic Z_m ⋊_r Z_k: every scaling (a, j) ↦ (ua, j) acts trivially on the quotient Z_k (and a faithful
     action r forces this). Z_337 ⋊ Z_6 at (10,5) gave minimum cost 399 against μ = 52.5.
   - Z_n factors with gcd(r − 1, n) > 1 (e.g. n = 9, 18, 21 for k = 3) put several z-values in Fix and project orbits
     onto a fixed quotient Z_p. Hence the rule: every prime factor of n is ≡ 1 mod k.
3. **Fixed points cost e^(−λ/k) each.** In SL(2,q) a conjugation has |Fix| = |C(g)| ≈ q ± 1 (a torus). With
   λ ≈ 7–10 at D = 7–8 that is 0.03–0.1 per fixed point for k = 3, but 0.14–0.25 for k = 5 and 0.24–0.37 for
   k = 7. That is why k = 3 is the useful case in SL-type groups.
4. **Fixed-point-free α exists only in nilpotent groups** (Thompson). The natural candidates, Heisenberg groups
   Heis(q) × Z_n with (x, y, z) ↦ (ax, by, abz), have |Fix| = 1. But at D = 8 they mix far too badly: random S has
   cost 1,500–7,000 at μ = 13–44, against ~25 for PSL/SL groups of the same order. Words that differ by a
   reordering collide modulo the centre. (They work at D = 5: our Δ9·D5 record is Heis(11).)
5. **One orbit is too few.** For Δ = 6 the only odd choices are f = 3, k = 3, m = 1 or f = 1, k = 5, m = 1. The
   orbit space then has only N·|Fix|² points and random symmetric S are poor (minimum cost 72 at μ = 30 at (6,8)).

So the working recipe is: **G = Q × Z_n with Q = SL/PSL/PGL(2,q) (or a product of two), every prime factor of n
≡ 1 mod 3, α = (conjugation by an element of order 3) × (z ↦ rz with r of order 3), k = 3**. Then Δ = f + 3m with
f ≥ 1. Use f = 1 when Δ ≡ 1 mod 3 (7, 10, 13, 16), f = 2 when Δ ≡ 2 (8, 11, 14), and f = 3 when Δ ≡ 0 (9, 12, 15),
the extra fixed generators being torus elements.

<!-- SECTIONS 3-6 -->
