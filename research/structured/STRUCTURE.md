# Structured generator sets for Haar graphs: what changes the exponent, and what does not

structured-search job (Opus), 2026-10-23, cloud container (4 cores, Xeon 2.8 GHz). Programs: `haar_sym.c`
(search), `tools/orb_screen.py` (screening), `tools/orbq.sh` (job queue). Notation follows `../frontier/SIZE_LAW.md`:
N = |G|, W = W(Δ,D) the number of binding words, λ = W/N, μ = N e^(−λ) the Poisson mean of the uncovered count.

## 0. Summary

1. **Orbit-symmetric S changes the exponent.** Make S invariant under an automorphism α of odd prime order k:
   S = {e} ∪ (generators fixed by α) ∪ (α-orbits of size k). The uncovered set then comes in α-orbits. A random
   symmetric S covers everything with probability ≈ e^(−μ/k − fixed-point misses) instead of e^(−μ). With k = 3
   (conjugation by an element of order 3 on SL/PSL(2,q), times z ↦ rz on Z_n), annealing over orbit
   representatives needs ≈ e^(μ/4.5) evaluations instead of ≈ e^(μ/2). On identical groups and seeds at (7,8):
   - μ = 34: random S 0/4 (cost 6 after 1.2–1.6·10⁶ evaluations); orbit 4/4 in 1.7–5.8·10⁴;
   - μ = 43: orbit solves in 2.3·10⁵; random S is at cost 9–10.
   The reachable μ roughly doubles (walls at μ ≈ 45–50 instead of 21–25 with ~10⁷ evaluations), which is
   +5–11 % in N.
2. **New graphs** in 15 cells, files in ../frontier/sols/ (names contain `orb3`); see §4. Every one passed
   haar_sym's full check and build_haar2.py. Above 20M vertices the independent low-memory checkers were used instead
   (two for SL, one for PSL). Gains are +2.4 % to +11 % over our previous records. Small gains in the biggest cells reflect compute, not the method: there only
   the first, cheap rungs (μ ≈ 8–15, a few hundred evaluations at 0.1–1 s each) were run. All are cells we already held;
   no new cell yet (§7).
3. **What does not work** (§2, §5): involutions (k = 2) and anything acting trivially on a quotient (z-only,
   metacyclic scalings, Z_n with fixed z) create word collisions. Heisenberg groups (fixed-point-free α) mix far too
   badly at D = 8. Frobenius (field) orbits, single orbits (Δ = 6), coset-structured S and big cyclic factors also
   fail.
4. **The ceiling does not move.** Counting symmetric S gives the same first-moment ceiling μ ≈ Δ ln N as random S
   (§1). Cells whose table lies above it ((12,8), (14,8), (16,8), D = 7 with Δ ≥ 9, D = 5 with Δ ≥ 13) stay
   unreachable for random-like and orbit-symmetric S alike. (10,8) and (11,8) lie below it and were attempted
   (§7). (11,8) got to 2 uncovered elements, both fixed by α. Neither cell is solved yet.
5. **"A billion times more efficient?"** (§6) Not as a constant factor: SPEEDUP.md measures 1.2–3.2× per core. As an
   exponent change, the orbit method beats extrapolated random-S annealing by ~10⁵ at μ = 34, ~10⁶ at μ = 43 and,
   extrapolated, ~10⁹ near μ ≈ 67. But it has its own wall, and nothing random-like passes the first-moment
   ceiling.


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

6. **Odd D: avoid groups with many involutions.** For odd D the binding word set on each side is inverse-closed
   (SIZE_LAW §2.3.4), so the words hitting an involution x = x⁻¹ come in collapsed pairs. x is then missed with
   probability e^(−λ/2), like a fixed point of an order-2 symmetry. PSL(2,q) has ≈ q²/2 involutions, SL(2,q) has one
   (−I). The expected involution misses, ~43–46 at (11,9), (13,9) and (16,9) with PSL(2,q) alone, match what was
   seen. Random S on PSL(2,397) at (13,9) has median cost 135 at μ = 9.6, and the orbit runs on PSL(2,257),
   PSL(2,397) and PSL(2,683) stalled at cost 59–73. At even D, PSL is fine (PSL(2,389) solved (10,10) in 385
   evaluations). This is the mechanism behind SIZE_LAW's empirical "avoid simple groups alone".

So the working recipe is: **G = Q × Z_n with Q = SL/PSL/PGL(2,q) (SL for odd D; or a product of two), every prime factor of n
≡ 1 mod 3, α = (conjugation by an element of order 3) × (z ↦ rz with r of order 3), k = 3**. Then Δ = f + 3m with
f ≥ 1. Use f = 1 when Δ ≡ 1 mod 3 (7, 10, 13, 16), f = 2 when Δ ≡ 2 (8, 11, 14), and f = 3 when Δ ≡ 0 (9, 12, 15),
the extra fixed generators being torus elements.

## 3. Calibration: how far up in μ does it reach?

All runs: haar_sym, k = 3, K = 8, single thread, this container (shared by up to 5 jobs). "evals" = cost evaluations
until cost 0, or the budget when it stopped. For comparison, random-S annealing (SIZE_LAW §4.1, (7,8), haar_gen3
on a Mac): μ = 13 solves in ~10⁵ evaluations, μ ≈ 21 needs ~5·10⁶, μ ≈ 30–34 failed 8 of 8 runs at 4.5·10⁶ each.
The fit there is evals ≈ 10⁵ e^((μ−13)/2).

| cell | group | N | μ | |Fix| | result | evals |
|---|---|---|---|---|---|---|
| (7,8) | psl 19 × Z13 (old record order) | 44,460 | 23.3 | 8 | solved 4/4 seeds | 0.7k, 1.3k, 3.1k, 3.6k |
| (7,8) | psl 17 × Z19 | 46,512 | 34.0 | 8 | solved 3/3 | 15.6k, 17.6k, 19.8k |
| (7,8) | psl 13 × Z43 | 46,956 | 36.7 | 5 | solved | 347k |
| (7,8) | psl 19 × Z14 | 47,880 | 43.0 | 17 | solved (**record**) | 264k |
| (7,8) | psl 11 × Z73 | 48,180 | 45.2 | 5 | best 3 | 3·10⁶ (stopped) |
| (7,8) | sl 11 × Z37 | 48,840 | 50.3 | 11 | best 1 | 5.9·10⁶ |
| (7,8) | prod psl 5 sl 5 × Z7 | 50,400 | 64.2 | 17 | best 6 | |
| (7,8) | sl 37 | 50,616 | 66.4 | 35 | best 10 | |
| (8,7) | psl 13 × Z19 | 20,748 | 27.8 | 5 | solved | 18k |
| (8,7) | sl 8 × Z43, pgl 8 × Z43 | 21,672 | 38.5 | 8 | solved (**record**), 5/5 seeds | 1.9k–183k |
| (8,7) | pgl 9 × Z31 | 22,320 | 47.6 | 8 | best 9 | 8.7·10⁶ |
| (8,8) | psl 17 × Z43 (an old record order) | 105,264 | 11.4 | 8 | solved 2/2 | 0.4k, 0.6k |
| (8,8) | psl 23 × Z19 | 115,368 | 27.9 | 11 | solved | 8.2k |
| (8,8) | sl 49 | 117,600 | 33.3 | 47 | solved | 1.0·10⁶ |
| (8,8) | psl 17 × Z49 | 119,952 | 39.8 | 8 | solved (**record**) | 88k |
| (8,8) | sl 11 × Z91 | 120,120 | 40.3 | 11 | best 4 | 6.0·10⁶ |
| (8,8) | prod sl 7 psl 9 | 120,960 | 43.0 | 53 | best 8 | 1.4·10⁶ |
| (8,8) | psl 19 × Z37 | 126,540 | 63.8 | 8 | best 9 | 3.9·10⁶ |
| (7,9) | psl 23 × Z37 | 224,664 | 28.5 | 11 | solved | 183k |
| (7,9) | psl 29 × Z19 | 231,420 | 38.2 | 14 | solved (**record**) | 1.5·10⁶ |
| (9,8) | sl 27 × Z13 (f = 3) | 255,528 | 21.6 | 53 | solved (**record**) | 504k |

Head-to-head on the same machine, same groups, same seeds 1–4, 60 s wall clock each (`tools/cmp.sh`, log `runs/cmp1.txt`;
the box ran 5–7 jobs, so 60 s bought 0.6–1.9·10⁶ evaluations):

| cell | group | N | μ | random S: solved, evals (or best cost) | orbit k=3: solved, evals |
|---|---|---|---|---|---|
| (7,8) | psl 19 x Z_13 | 44,460 | 23.3 | 1/4; best 2 @ 1.9e+06, best 1 @ 1.7e+06, best 2 @ 1.7e+06, 3.28e+04 | 4/4; 3.62e+03, 3.14e+03, 1.33e+03, 737 |
| (7,8) | psl 17 x Z_19 | 46,512 | 34.0 | 0/4; best 6 @ 1.2e+06, best 6 @ 1.4e+06, best 6 @ 1.6e+06, best 6 @ 1.3e+06 | 4/4; 1.67e+04, 5.76e+04, 2.65e+04, 3.76e+04 |
| (7,8) | psl 19 x Z_14 | 47,880 | 43.0 | 0/4; best 10 @ 8.4e+05, best 9 @ 9.8e+05, best 9 @ 6.4e+05, best 10 @ 7.9e+05 | 1/4; 2.29e+05, best 3 @ 6.5e+05, best 3 @ 7.1e+05, best 3 @ 7.9e+05 |

Reading: for k = 3 the evaluations to solve grow roughly like e^(μ/4.5) (from 3·10³ at μ = 23 to 3·10⁵ at μ = 43
at (7,8)), against e^(μ/2) for random S. The wall, the μ where ~10⁷ evaluations stop sufficing, is μ ≈ 45–50 at
N ≈ 2·10⁴–10⁵. For random S it is μ ≈ 21–25. Runs that stall usually sit at cost 1–9: one or two uncovered orbits
plus fixed points (cost ≢ 0 mod 3 means a fixed point is uncovered).

## 4. New graphs (haar_sym's full diameter check, plus build_haar2.py or the low-memory checkers; files in ../frontier/sols/)

<!-- generated by tools/records_table.py from runs/ -->
| cell | table (DS14v2) | our previous best | new | group, structure (k, m, f) | μ at new order | evals | file (../frontier/sols/) |
|---|---|---|---|---|---|---|---|
| (6,7) | 8,310 | 8,440 | **8,880** (+5.2 %) | sl 5 × Z37; 3, 2, 0 | 54.6 | 5e+02 | d6D7_sl_5_37_orb3f0_s2.txt |
| (8,7) | 40,586 | 41,040 | **43,344** (+5.6 %) | sl 8 × Z43; 3, 2, 2 | 38.5 | 1.2e+04 | d8D7_sl_8_43_orb3_s1.txt |
| (7,8) | 80,940 | 88,920 | **95,760** (+7.7 %) | psl 19 × Z14; 3, 2, 1 | 43.0 | 2.6e+05 | d7D8_psl_19_14_orb3_s1.txt |
| (8,8) | 201,480 | 225,792 | **239,904** (+6.2 %) | psl 17 × Z49; 3, 2, 2 | 39.8 | 8.8e+04 | d8D8_psl_17_49_orb3_s1.txt |
| (9,8) | 449,480 | 497,904 | **524,160** (+5.3 %) | prod sl 5 psl 7 × Z13; 3, 3, 0 | 28.0 | 2.4e+05 | d9D8_prod_sl_5_psl_7_13_orb3_s1.txt |
| (13,8) | 5,314,680 | 6,408,480 | **6,604,416** (+3.1 %) | prod sl 8 sl 8 × Z13; 3, 4, 1 | 23.9 | 5.3e+04 | d13D8_prod_sl_8_sl_8_13_orb3_s1.txt |
| (7,9) | 400,160 | 416,640 | **462,840** (+11.1 %) | psl 29 × Z19; 3, 2, 1 | 38.2 | 1.5e+06 | d7D9_psl_29_19_orb3_s1.txt |
| (8,9) | 1,091,232 | 1,245,312 | **1,316,016** (+5.7 %) | sl 37 × Z13; 3, 2, 2 | 23.9 | 2.2e+05 | d8D9_sl_37_13_orb3_s1.txt |
| (10,9) | 7,057,400 | 7,488,000 | **8,003,856** (+6.9 %) | sl 83 × Z7; 3, 3, 1 | 22.2 | 2.5e+04 | d10D9_sl_83_7_orb3_s1.txt |
| (11,9) | 15,200,448 | 16,369,920 | **16,792,080** (+2.6 %) | sl 61 × Z37; 3, 3, 2 | 15.0 | 5e+03 | d11D9_sl_61_37_orb3_s1.txt |
| (13,9) | 50,990,610 | 62,156,160 | **63,872,400** (+2.8 %) | sl 101 × Z31; 3, 4, 1 | 13.3 | 2.8e+02 | d13D9_sl_101_31_orb3_s1.txt |
| (14,9) | 95,087,738 | 111,482,880 | **116,068,656** (+4.1 %) | sl 67 × Z193; 3, 4, 2 | 14.1 | 3.4e+03 | d14D9_sl_67_193_orb3_s1.txt |
| (16,9) | 288,939,118 | 316,679,760 | **324,164,400** (+2.4 %) | sl 149 × Z49; 3, 5, 1 | 7.1 | 9 | d16D9_sl_149_49_orb3_s1.txt |
| (7,10) | 1,987,380 | 2,147,040 | **2,234,400** (+4.1 %) | psl 49 × Z19; 3, 2, 1 | 22.2 | 2.3e+04 | d7D10_psl_49_19_orb3_s1.txt |
| (8,10) | 6,927,210 | 7,349,616 | **7,802,160** (+6.2 %) | sl 59 × Z19; 3, 2, 2 | 22.4 | 7.4e+04 | d8D10_sl_59_19_orb3_s1.txt |
| (10,10) | 50,331,156 | 57,868,272 | **60,141,120** (+3.9 %) | sl 79 × Z61; 3, 3, 1 | 15.3 | 8.3e+02 | d10D10_sl_79_61_orb3_s1.txt |
| (13,10) | 617,330,936 | 636,550,992 | **657,485,136** (+3.3 %) | sl 197 × Z43; 3, 4, 1 | 12.0 | 6.6e+02 | d13D10_sl_197_43_orb3_s1.txt |

Graphs above 20M vertices were checked by independent low-memory checkers instead of build_haar2.py, as in
SIZE_LAW §3.2: SL(2,p) × Z_n by both `../frontier/haarcheck_sl.c` and `../frontier/haarcheck2.c`, PSL(2,p) × Z_n
by `tools/haarcheck_psl.c` (written here; it agrees with build_haar2.py on 5 smaller PSL graphs). Outputs are in
runs/*.lowmem.txt or at the end of each log.

Every other VALID solution of this job (lower rungs of the same ladders, kept for the record) has its log in
runs/. Some of those are also in ../frontier/sols/ (e.g. (7,9) 449,328, (8,9) 1,279,680 and 1,308,720, (8,10)
7,432,152 and 7,596,840, (10,9) 7,596,840 and 7,802,160, (13,8) 6,434,112). The edge-list sha256 of each graph is in
its log (last lines, from build_haar2.py) or in runs/*.rebuild.txt.

<!-- MORE-RECORDS -->

## 5. Negative and screening results (structured families that do not help)

| family | test | result |
|---|---|---|
| involutive α (k = 2), any Q × Z_n | RANDORB, ball growth, brute force on SL(2,13) × Z19 | median cost 400–500 against μ = 12.7 (random S: 31); length-2 words already collide (41 or 39 distinct instead of 43): α(u) = u⁻¹ for a density-1/q set |
| α trivial on Q (z ↦ −z only) | RANDORB | cost 10⁴–3·10⁴ at μ = 12.7 |
| conjugation only, z fixed (AR = 1) | RANDORB | median 401 at μ = 12.7; |Fix| = 227 |
| metacyclic scaling (a, j) ↦ (ua, j) | Z_337 ⋊ Z_6 at (10,5) | min 399 against μ = 52 (random S min 178); α is trivial on the quotient Z_6 |
| AGL(1,223) with conjugation | (7,8) | cost ≈ 40,000: degenerate |
| Heisenberg groups Heis(q) × Z_n (fixed-point-free α) | (7,8), (8,8) RANDSAMPLE | random S already costs 1,500–7,900 at μ = 13–44 (SL-type: ~25–80): class-2 nilpotent groups mix badly at D = 8 |
| field structure: Frobenius orbits, x ↦ x^p entrywise on SL(2,8) × Z43 | (8,7), 3 seeds × 60 s | best cost 10 every time (1.5·10⁶ evals each); conjugation orbits on the same group solve in 2·10³–2·10⁵ evals |
| one orbit (m = 1), Δ = 6 | (6,8), k = 3 (f = 3) and k = 5 (f = 1) | min 72 / 38 at μ = 30 (median 342 / 7,860); orbit space too small |
| large cyclic factor Q × Z_p, p ≈ 300–800 | (10,8), (11,8) with k = 5 | random S min 75–300 at μ = 62–71 (sl 9 × Z821 worst); also no wide rows |
| PSL(2,q) alone at odd D (involutions) | (11,9) psl 257, (13,9) psl 397, (16,9) psl 683 | stalled at cost 73, 59, 68 (μ = 17.5, 9.6, 5.2); random S median 135 at μ = 9.6; predicted involution misses ≈ 43–46 |
| coset-structured S (S ⊂ xH, unions of cosets of a torus/unipotent subgroup) | algebra | s_i⁻¹ s_j ∈ H for all pairs: length-2 words collapse into a small subgroup (no run needed) |

What the negatives have in common: **any structure that makes words collide is fatal**, because coverage is only
~λ ≈ 8–15 words per element. Equivariance (orbits) works because it correlates *which* elements are covered without
creating collisions, as long as α has odd order and acts without fixed points on every quotient.

Singer difference sets fit this picture. By Hall's multiplier theorem a perfect difference set in Z_(q²+q+1) is
fixed, up to translation, by the multiplier z ↦ q z, an automorphism of order 3. So the D = 3 Moore construction is
itself an orbit-structured S. At D = 3 the orbit structure gives zero waste. At D ≥ 7 it only reshuffles the
Poisson clumps, which is why the gain is in search effort and not in the ceiling.

## 6. Can the algorithm be made a billion times more efficient? (the honest answer)

**As a constant factor: no.** SPEEDUP.md measures 1.2–3.2× per core end to end, bit-identical. The bitset BFS is
within 2–3× of the memory system's limit on this CPU. A GPU might add 10–30×, and 4 cores give 4×. That is 10²–10³
at best. Since each 10× in evaluations buys ≈ +4.6 in μ ≈ +3–4 % in N (SIZE_LAW §4.1), even 10⁹ would buy only
≈ +30 % in N. The cells asked about need far more than that:

| cell | table | μ at table | first-moment ceiling μ_h = Δ ln N | random-S evals ≈ 10⁵ e^((μ−13)/2) | status |
|---|---|---|---|---|---|
| (10,8) | 1,176,480 | 62.6 | 133 | 6·10¹⁵ | below the ceiling |
| (11,8) | 2,246,940 | 56.9 | 154 | 3·10¹⁴ | below the ceiling |
| (12,8) | 4,650,100 | 230 | 175 | — | above the ceiling |
| (14,8) | 14,172,480 | 483 | 221 | — | above the ceiling |
| (16,8) | 36,201,060 | 733 | 267 | — | above the ceiling |

(The ceiling is the μ where the expected number of valid S, ≈ N^Δ e^(−μ), drops to 1; table/2N_h > 1 in
SIZE_LAW §3.3.)

**As an exponent: partly yes.** Orbit-symmetric S with k = 3 replaces e^(μ/2) by about e^(μ/4.5) (§3). At μ = 34 it
needed 2·10⁴ evaluations where random-S annealing needs ~4·10⁹ (extrapolated; it failed at 4.5·10⁶): a factor of
~10⁵. At μ = 43, 3·10⁵ against ~3·10¹¹: ~10⁶. Extrapolating both fits (random 10⁵ e^((μ−13)/2), orbit
3·10³ e^(0.226(μ−23.3))), the ratio ≈ 10 e^(0.274 μ) reaches 10⁹ at μ ≈ 67. In that sense the change *is* a
billion-fold efficiency gain around μ ≈ 65–70, but only there:

- **It cannot pass the first-moment ceiling.** The count of symmetric S shrinks by the same factor k in the exponent
  (§1), so (12,8), (14,8) and (16,8), whose tables lie *above* the ceiling for every random-like or orbit-symmetric S
  (and likewise D = 7 with Δ ≥ 9 and D = 5 with Δ ≥ 13), stay out of reach at any compute. Those tables come from
  algebraic constructions whose words cover with negative correlation (§4.3 of SIZE_LAW). Nothing in this job
  reproduces that at D ≥ 7.
- **It has its own wall**, at μ ≈ 45–50 with 10⁷ evaluations for k = 3 (§3), set by μ/3 plus fixed-point misses.
  Larger k needs α with few fixed points. In SL-type groups |Fix| ≈ q and each fixed point is missed with probability
  e^(−λ/k). Groups with fixed-point-free α are nilpotent and mix badly (§5).
- (10,8) and (11,8) lie in the band between the k = 3 wall and the ceiling. Both were attempted (§7): (10,8) with
  k = 3 (μ_eff ≈ 22, best 12) and (11,8) with k = 5 on PSL(2,59) × Z11 (μ_eff ≈ 16, best 2: only fixed points
  left). Neither is solved. (11,8) looks close.

## 7. Open attempts, and what to do next

- **(10,8)**, new cell, table 1,176,480 (needs N ≥ 588,241, μ ≥ 62.6). k = 3 on psl 23 × Z97 (N = 588,984,
  μ_eff ≈ 21 + 0.6): best cost 12 (= 4 uncovered orbits) after 2.7·10⁶ evaluations (34 min). Not solved. By the
  §3 fit it needs ~2·10⁷ or more. k = 5 (Δ = 5·2, f = 0) would give μ_eff ≈ 14, but every group with elements of order 5
  and a suitable Z_n at this order has a large cyclic factor and mixes badly (sl 9 × Z821: random-S minimum 298 at
  μ = 66; sl 11 × Z451: orbit minimum 78).
- **(11,8)**, new cell, table 2,246,940 (needs N ≥ 1,123,471, μ ≥ 56.9). k = 5 (Δ = 1 + 5·2) on psl 59 × Z11
  (N = 1,129,260, μ = 60.2, μ/5 = 12.0, |Fix| = 29, expected fixed-point misses 4.2):
  - seed 1: best cost 3 after 3.0·10⁶ evaluations (2 h);
  - seed 2 with RESTART=1: best 2 after 1.6·10⁶ (1 h).
  Free orbits come in multiples of 5, so both runs had **all free orbits covered**; what remained were 2–3
  uncovered α-fixed elements. The run was decided by fixed points, as §2.3 predicts. A short try on psl 19 × Z331
  (|Fix| = 10 but no wide rows, 7 ms per evaluation) reached cost 15. Promising next steps: a group with a smaller
  centralizer and good mixing, more seeds, or extra fixed generators to cover Fix(α). The cell looks within reach.
<!-- OPEN-ATTEMPTS -->

Next steps, in order of expected value:
1. **Push the held cells further.** Done here: the 15 cells of §4. The large cells (N ≥ 10⁷) only got rungs at
   μ ≈ 5–17, which cost 25–5,000 evaluations. Going up to μ ≈ 25–35, as at the smaller cells, would add another
   3–6 % there, at 0.1–2.5 s per evaluation (hours per cell). Not run at all: (13,10), (14,10), (12,10), (9,9),
   (9,10), (12,9), (15,9), (15,8) and (6,*), where Δ ≡ 0 mod 3 or Δ = 6 or memory (N ≥ 3·10⁸) is the obstacle.
   Recipe: `tools/orb_screen.py` (or SL(2,p) × Z_n with every prime of n ≡ 1 mod 3; SL for odd D) and `tools/orbq.sh`
   with a μ-ladder starting just above our current order.
2. **Δ ≡ 0 mod 3 is weak** (f = 3: two extra torus generators, an abelian sub-alphabet). (9,8) went +2.6 % and then
   stalled at μ = 27. Better choices for Δ = 9, 12, 15 would need k = 5 or 7 with fewer fixed points.
3. **Groups with small centralizers and good mixing.** The k = 3 wall is μ/3 + |Fix|·e^(−λ/3) ≈ 16–18. In SL(2,q),
   |Fix| ≈ q, which blocks k ≥ 5 except when q is small (but then n is large and mixing is poor). SL(3,q) has
   regular-semisimple centralizers of size ~q² out of q⁸, which would allow k = 5–7 at moderate N. Not implemented
   (needs a 3×3 matrix family in haar_gen3/haar_fast and in build_haar2.py).
4. **A cheaper orbit evaluation.** If the coset subgroup H lies in Fix(α) = C(g) × {0}, then α maps the coset
   x H to α(x) H with a fixed rotation, and the frontier rows of an α-orbit of rows are rotations of each other. Keep
   only one representative row per orbit, and fold the map "source row → (representative, extra offset)" into each
   generator's table when it is built (offsets add, so a gather still costs one window read). Then tables, dense
   levels and counting all shrink by about k. It needs |C(g)| ≥ 64 for wide rows, i.e. q ≥ 64. It does not apply
   to the q = 23 and q = 59 groups used for (10,8) and (11,8) here. Worth ≈ +2 in μ for k = 3 and ≈ +3 for k = 5.
5. **Above-ceiling cells** ((12,8), (14,8), (16,8), D = 7 with Δ ≥ 9, D = 5 with Δ ≥ 13). They need covering-design
   structure (negatively correlated coverage). The natural route is voltage lifts over Moore graphs or generalized
   polygons with structured voltages (Loz–Pérez-Rosés–Pineda-Villavicencio style). That is a different program and
   was not attempted here.


## 8. Free orbits only (f = 0): the fix for Δ ≡ 0 mod 3 and Δ = 6 (second session)

Second structured-search session, 2026-10-23 evening, same container type (4 cores, now not shared).

**The idea.** With k = 3, Δ = f + 3m forced f = 3 when 3 | Δ: S = {e, t₁, t₂} ∪ O₁ ∪ … ∪ O_m with t₁, t₂ in the
torus C(g). Those three letters commute, so every run of ≥ 3 consecutive fixed letters in a word can be reordered
without changing its value: a built-in source of word collisions. And Δ = 6 had only f = 3, m = 1 (one orbit, §2.5).
But e ∈ S is only a normalisation (H(G,S) ≅ H(G,S·x⁻¹)). So take **f = 0**: S = O₁ ∪ … ∪ O_(Δ/3), no identity, no
α-fixed letter at all. α still fixes (e,A) and (e,B), the uncovered set is still a union of α-orbits, and the words
hitting a fixed point still come in α-orbits of 3, so §1's μ_eff = μ/3 + |Fix|·e^(−λ/3) is unchanged. What changes is
that no letters commute and there are Δ/3 orbits instead of Δ/3 − 1. haar_sym already accepted `ORBIT="3 m 0"`
(it writes S·s₀⁻¹ so the file starts with e, after re-running its full check); it had never been run.

**Ball growth** (distinct elements per BFS level, 3 random symmetric S each, (9,8) on PSL(2,23) × Z43; the
non-backtracking word count is 9, 73, 585, 4,681, 37,513, …):

| f | level 2 | level 3 | level 4 | level 5 | level 6 | RANDORB median cost (μ = 26.9) |
|---|---|---|---|---|---|---|
| 3 (e, t₁, t₂ + 2 orbits) | 71–73 | 553–569 | 4,228–4,365 | 30,632–31,329 | 156,534–160,908 | 225 |
| 0 (3 orbits) | 73 | 576–585 | 4,477–4,645 | 32,964–34,677 | 169,703–173,191 | 68 |

f = 3 loses 8–10 % of the words at levels 4–6 to collisions; f = 0 loses 1–3 %.

**Head-to-head** (`tools/cmp.sh`, same seeds, wall clock, 4 single-thread runs at a time):

<!-- F0-CMP -->

**What it found** (all in §4): (9,8) 511,056 → **524,160** (first f = 0 run: PSL(2,23) × Z43 = 522,192 in 521 and
1.5·10⁵ evaluations, where f = 3 had stalled at cost 3 after 1.9·10⁶; then SL(2,5) × PSL(2,7) × Z13); (6,7) 8,440 →
**8,880** (SL(2,5) × Z37, 505 evaluations; even above the first-moment estimate 2N_h ≈ 8,747 of mu_plan.py).

**Where it does not help.** (6,8) on PSL(2,9) × Z43 (μ = 28.2, just above our 30,576): f = 0 stops at cost 3 (one
uncovered orbit) after 6·10⁷ evaluations, random S at cost 2 after 6.6·10⁷ (2 seeds each, 600 s). With m = 2 the
orbit space has only (N/3)²/2 ≈ 1.3·10⁷ points, fewer than the evaluations spent: Δ = 6 is at the orbit method's
first-moment ceiling there.
