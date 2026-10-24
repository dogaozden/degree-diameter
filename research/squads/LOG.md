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
