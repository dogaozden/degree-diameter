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
