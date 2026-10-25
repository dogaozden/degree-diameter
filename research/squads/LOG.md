# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 19:00 UTC, cell-10-8 session, goal: beat (10,8) table 1,176,480, round d10D8-r1

Cards (scoreboard research/squads/d10D8-r1/scoreboard.jsonl):
- c1 hexagon lift H(q) + 2 matchings, Z_r hexagon voltages × Z5 levels: c_max(2) = 45, c_max(3) ≥ 25 (formula 15, 20), APSP-verified. Score 25.
- c2 same, free voltages / Z_m levels: q=3 m=20 valid, q=3 m=30 and q=4 m=20 not. Score 0.
- c3 nonabelian voltage groups: q=4 best A4 (order 12); order 16 near misses. Score 12.
- c4 q=7 scaling probe of hexagon lifts (pending).
- c5 Haar group screen for k=3/k=5 in the window (pending).
- c6 annealer schedule on proxy psl 25 × Z73: nothing solved in 120 s (best 4–9); COOL=10 REHEAT=60 weakly best. Score: censored.
- c7 wildcard: PG(2,9) incidence graph lifted by Z4000: valid at (10,8) with 728,000 vertices (0.62 of the table).
- c8 hubs on the Z10 hexagon lift at q=3: +15 vertices, APSP-verified (7,295 vs 7,280); does not close the 3× gap at q=7.
Kept: nothing beats the cell. The small-q slack of the hexagon family (c1) does not transfer: at q = 7 a random-like
voltage assignment has ~3·10⁶ uncovered (source, target, sheet) triples against ~2·10⁵ free variables (cell notes §3).
Lesson: 8 Haiku cards with their own test runs slowed the 3 main haar_sym runs about 4× (memory contention), so the
next round has to be lighter. Next: 4th main run; duplicate-word analysis (ZOPT, research/d10D8/zopt/).

## 2026-10-24 19:20 UTC, cell-10-8 session, goal (10,8), round d10D8-r2 (4 light analysis cards, strict CPU caps)

Cards (research/squads/d10D8-r2/scoreboard.jsonl):
- r2-c1 rank 46 prime-n groups by μ_eff = μ·e^(δλ) (δ = measured duplicate rate): Spearman 0.82 with the RANDORB p1,
  but the two best lower tails are psl 23 × Z97 (p1 54) and PSL(2,7) × SL(2,8) × Z7 (p1 50) — the two groups the main
  runs use. Kept: no switch.
- r2-c2 cheap features predicting a low duplicate rate: duplicates among words of length ≤ 5 (1/80 of the work)
  predict the full rate with Spearman 0.986; element orders, traces etc. do not (|ρ| ≤ 0.23). Among annealed good
  states the duplicate rate (7.5–8.8 %) does not track the cost, so no filter for the annealer.
- r2-c3 explicit (non-annealed) hexagon voltage rule: flag voltage 6·p·l mod 16 (hexgen2 indices), σ1 = identity
  numbering (voltage 1), σ2 = shift by N/3 (voltage 6) is valid at q = 2, 3, 4 with 16 levels (independent BFS agrees
  at q = 4); the formula's 20 at q = 4 was not reached (best 2 misses at 18 and 20). Score 0.8. Nothing points to
  30+ levels at q = 7.
- r2-c4 wildcard group families: best is again PSL(2,7) × SL(2,8) × Z7 (5000-sample p1 50–51 against 55–57 for
  psl 23 × Z97 over seeds 1–3, p10 75–76 against 82–84); A5 × PSL(2,27), A5 × PSL(2,13) × Z9, PSL(2,7)² × Z21,
  SL(2,32) × Z18, PSL(2,53) × Z8, a Frobenius α on the SL(2,8) factor and twisted PGL groups are all worse.
Main runs meanwhile: PSL(2,7) × SL(2,8) × Z7 reached cost 7 in 5.8·10⁵ evaluations, below anything PSL(2,23) × Z97
reached in 4.5·10⁶ (best 9); three main runs moved to that group (one with ORBW=3).

## 2026-10-25 10:50 UTC, cell-10-8 session (resumed), goal (10,8) 1,176,480, round d10D8-r4

(Round r3 was briefed by the previous session but never launched; its brief became card c5 here.)
Cards (research/squads/d10D8-r4/scoreboard.jsonl; scorer: chain minima of 8-minute fresh-descent runs on
PSL(2,7) × SL(2,8) × Z7, baseline median 17, best 12):
- c1 more candidates per step: K = 24 median 16 (best 15), K = 48 median 20 (best 12). Neutral.
- c2 targeting/temperature: TARGP 95 + TMIN 0.08 median 18; TARGP 50 + flatter T median 21. Neutral or worse.
- c3 crossover of 20 good states (2 orbits of A + 1 of B, 3,420 sets): best 24, median 99, all worse than both parents
  (each crossover is a one-orbit replacement of a good state). Negative.
- c4 replica exchange (4 replicas, T 0.15–1.2): best 15 in 8 min. Not better.
- c5 explicit hexagon voltages from PG(6,q) coordinates: valid at q = 3 with 19 levels (formula 20); nothing at q = 4.
  Nothing toward 30+ levels at q = 7.
- c6 tail analysis of the descent statistics (see below).
- c7 iterated local search (one random-orbit kick, re-descent from T 0.4/0.8): chain minima 12 13 14 17 18; a kick
  costs 55–250, so each kick is a restart. Not better.
- c8 wildcard, larger symmetry on PSL(2,23) × Z97: Z6 = ⟨α, conjugation by the commuting involution⟩ gives random cost
  ≥ 315 (median 10,934) because s and β(s) share their Z97-part; a single Z3 × Z3 orbit caps the reachable set
  (min cost 496,991). Negative.
Also tried by the lead this round: inverse-closed S (INVPAIR, random cost ≥ 5,888: e ∈ S collapses words), exhaustive
best-response descent (EXDESC: local optima 14–15 in 7–11 min, cost-7 state is an exact local optimum), a non-identity
α-fixed letter instead of e (F0: RANDORB unchanged, median 128–131).
Kept: nothing beats plain short fresh descents. The search draws isolated good states; volume is the only lever left.
