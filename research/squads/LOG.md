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
