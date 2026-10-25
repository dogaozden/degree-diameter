# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-15-10 (Opus 5.5, cloud session), goal: beat (15,10) = 2,300,326,510

Context before the squads: Opus wrote research/lowmem/haar_lean.c (orbit search with a two-bitset evaluator, 0.3 GB
at N = 1.2·10⁹) and got 2,325,625,680 (SL(2,139) × Z433, μ = 5.7, 17 evaluations) and 2,454,528,720
(SL(2,139) × Z457, μ = 16.4, 377 evaluations), both self-checked; higher rungs running (μ = 18.2, 23.7).

### Round d15D10-r1 (19:27 UTC, 8 cards, scoreboard research/squads/d15D10-r1/scoreboard.jsonl)
Question of the round: what raises the reachable μ at (15,10)? Screening at full scale by the cost of random
symmetric S (RANDORB; big runs serialized through one lock), and search parameters on a (15,8) proxy.
- c1: SL(2,p) × Z_n, p ≡ 1 mod 3, μ 20–30, excess = median cost / μ.
- c2: same, p ≡ 2 mod 3.
- c3: PSL(2,p) × Z_n.
- c4: big p, tiny n (n ≤ 73, including n = 1), and the eval time there.
- c5: K (candidates per step) ∈ {4, 8, 16} on the (15,8) proxy SL(2,59) × Z43 (μ = 23).
- c6: ORBW ∈ {1, 3} × TARGP ∈ {70, 95} on the same proxy.
- c7: orbit size k = 5 ("5 3 0") vs k = 3 on groups that allow both.
- c8: wildcard (other α, RESTART/schedule, f = 3, ...).
Best score per card (excess = median cost of random symmetric S / μ; lower is better; noise about ±0.1–0.15 with 12–16
samples):
- c1: sl 307 × Z43 1.08 (μ 21.3); sl 457 × Z13 1.19; sl 139 × Z463 1.28; sl 127 × Z607 1.33; sl 79 × Z2521 1.87
  (mean 99.6: heavy tail).
- c2: sl 197 × Z163 **0.82** (μ 21.9, min 6); sl 137 × Z487 1.12; sl 107 × Z1021 1.28; sl 83 × Z2179 1.79.
- c3: psl 149 × Z751 1.07 (μ 20.6); psl 97 × Z2719 2.68 (mean 540).
- c4: big p, n ≤ 43: excess 1.03–1.18 (psl 1361, sl 457 × Z13, psl 709 × Z7, sl 307 × Z43, psl 431 × Z31), but
  1.5–3.7 s per evaluation for n ≥ 7 and 7.5 s for psl 1361 × Z1 (926k short rows), against ~1 s for p ≈ 140–200.
- c5: K on the proxy: K = 8 solved 2/3 (median 4,193 evals), K = 4 and K = 16 1/3 each. Within noise; keep 8.
- c6: ORBW = 1, TARGP = 70 (defaults) solved 2/2 (4,089–4,289 evals); ORBW = 3 solved 1/4. Keep the defaults.
- c7: k = 5 vs k = 3 at full scale: median 38 vs 30 (sl 181 × Z211), 35 vs 34 (sl 191 × Z181); proxy tie. Keep k = 3.
- c8: α choice is a no-op (ATRACE and r ↔ r⁻¹ give identical distributions; all order-3 conjugations are equivalent);
  AR = 1 (Z_n fixed) median 951, f = 6 median 615, f = 3 worse than f = 0 (mean ~50 vs ~32). Keep f = 0.
What I kept: the defaults (K 8, TARGP 70, ORBW 1, f 0, k 3); the rule "moderate n (100–800), p ≈ 130–200": big cyclic
factors give heavy tails, big p gives slow evaluations. What I did next: high rungs on sl 191 × Z181 (μ 27.5, my own
screen: mean 26.6) and psl 149 × Z763 (μ 27.8, sibling of c3's psl 149 × Z751); sl 181 × Z211 (μ 23.7) kept running.

## 2026-10-25, cell-15-10 resumed (Opus 5.5, cloud session 0173GYQo), goal: beat (15,10) = 2,300,326,510

State at resume: 2,325,625,680 independently VALID; 2,454,528,720 and 2,467,618,800 self-checked (k = 3 orbits on
SL(2,p) × Z_n). This session: haarcheck2 VALID on **2,467,618,800** (12:53 UTC, 1,072 s). Then a new idea: orbits of
size k = 5 on PSL(2,p) × Z_n. Model (STRUCTURE.md §1): P(cost 0) ≈ e^(−μ_eff), μ_eff = μ/k + F, F = |Fix| e^(−λ/k);
at (15,10) λ = W/N ≈ 17.6, so F costs only 0.03 per fixed point at k = 5, and PSL halves the torus (|Fix| = (p ∓ 1)/2).
First measurement (Opus, μ ≈ 26): random symmetric S have median 6–7 "units" (uncovered α-orbits + uncovered fixed
points) for k = 5 against ~11 for k = 3; k = 5 annealing reached cost 1–2 in ~400 evaluations where k = 3 sat at 10.

### Round d15D10-r2 (12:45 UTC, 8 cards, scoreboard research/squads/d15D10-r2/scoreboard.jsonl)
Question of the round: where does k = 5 work best? Score = median units of random symmetric S at full scale (RANDORB,
24 samples, one at a time through a lock), or evaluations to solve on the (15,8) proxy.
- c1: PSL(2,p), p ≡ 1 mod 5, μ 33–35. c2: p ≡ 4 mod 5. c3: composite n vs prime n. c4: tiny p (11–59) with huge n.
- c5: one orbit of size 15 (ORBIT "15 1 0", p = 29, 31). c6: proxy head-to-head k = 5 vs k = 3 on the same group.
- c7: k = 5 annealing parameters on the proxy. c8: does the Fourier spectrum A(S) of the z-parts explain the big-n penalty?
Best score per card:
- c1: psl 181 × Z431 median 10 units at μ 35.0 (μ_eff 9.8; tracks the model); psl 71 × Z7121 13 (μ_eff 7.7);
  p ≤ 61 with n ≥ 11,000: 15 to 6·10⁶.
- c2: psl 79 × Z5171, 89 × Z3631, 269 × Z131: 10–11 at μ 33–36; psl 59 × Z12421: 21 (heavy tail).
- c3: composite n keeps |Fix| at the torus size but is ~2 units worse than prime n at equal μ in 3 of 3 pairs
  (1–2 SE; suggestive). Best composite psl 89 × Z3641 12, its prime twin psl 89 × Z3631 10–11.
- c4: small p loses: psl 59 × Z12431 18, psl 41 21–61, psl 29/31 140–210, psl 11 × Z1.9M 4.6·10⁶ (abelian collapse).
- c5: k = 15 is dead: psl 31 × Z85021 median cost 92,808 (units 6,190) at μ 29.
- c6: proxy psl 31 × Z601 (μ 27.45): **k = 5 solved 3/3 (729, 2,985, 3,745 evaluations), k = 3 solved 0/3** (best 6–7
  after 32–35k). psl 19 × Z2671 (μ 36.6): neither solves in 120 s; units 20 vs 60.
- c7: proxy psl 19 × Z2651 (μ 33): nothing solved in 100 s with any of K 4/8/16, TARGP 40/70/95, ORBW 5 (best 1–10);
  the proxy with n ≈ 2,650 and p = 19 is too hard to tune on.
- c8: Spearman(cost, A) = 0.45 on the proxy (k = 5), 0.74 for k = 3, 0.32 at full scale (40 samples); the top A decile
  carries most of the effect (median cost 72 vs 140 between the lowest and highest A quartiles).
What I kept: k = 5 on PSL(2,p) × Z_n with p ≈ 130–200 and n a prime of a few hundred (excess ≈ 1, units ≈ μ/5 + F);
dropped k = 15, tiny p, composite n where a prime one exists. Opus also wrote FIXPRE (exact meet-in-the-middle test
of the α-fixed points before each full evaluation, 0.06 s against 1.3 s; validated against the evaluator on 60 samples),
which removes F from the exponent at the price of e^F cheap tests per candidate, and ZMAX (z-spectrum filter, not used
yet: small n makes it unnecessary). What I did next: four k = 5 FIXPRE runs at μ = 26.4, 35.0, 41.9, 43.3.
