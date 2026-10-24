# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, table-squad (Opus, cloud session), round 1: the D = 5 column with orbit-symmetric Haar graphs

Goal: records at D = 5, Δ = 6..15 (cells we don't hold except (7,5), (8,5), (9,5)). Opus calibration before the round:
`haar_sym` (research/structured, branch claude/structured-search-orbit-04hefm @ 1c20eb4) with ORBIT="3 3 0" solved
(9,5) on SL(2,11) (N = 1320) in 0.1 s, where plain annealing stalls at 2 uncovered after 12M evaluations. Fixed points
of α are the binding cost at D = 5 (e^(−λ/k) each, λ ≈ 3.5), and metacyclic/Heisenberg scalings fail (924 and 78
uncovered). Leads: (11,5) A5 × Z49, μ = 67, best 6 in 120 s; (10,5) SL(2,13), μ = 74, best 8.
Preamble shared by all cards: research/squads/r1/PREAMBLE.md.

Cards: c1 (10,5) SL(2,13)/PSL(2,7)×Z13 long runs + k=2 + screen · c2 (11,5) A5×Z49 long runs + k=2,5 + screen ·
c3 (12,5) screens for k = 3, 4, 6 with f = 0 · c4 (13,5) screens k = 3, 4, 6 with f = 1 · c5 raise ours at (7..9,5) ·
c6 (6,5) near-exhaustive RANDORB on groups of order 343..400 · c7 wildcard (14,5), (15,5) with large k ·
c8 wildcard: any non-default idea at (10..12,5).
