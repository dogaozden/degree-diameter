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

### Round 1 outcomes (reports so far)
- c5 raise (7..9,5): worse. (9,5) best 6 on PSL(2,7) × Z8 "2 4 1" (N 1344); (8,5) best 12 on S4 × Z37 "3 2 2" (N 888);
  (7,5) best 24 on A4 × Z49. Lesson: the minimum over random symmetric samples predicts where annealing stalls.
- c6 (6,5): failed. The orbit families are small enough to sample exhaustively: true minima 16 (A5 × Z7, N 420), 22–24
  (A6, SL(2,5) × Z3, N 360). Worse than earlier non-symmetric searches (2 uncovered): at Δ = 6, D = 5 symmetry costs too
  much freedom.
- c7 wildcard (14,5), (15,5): failed (best 444 and 132). Found a necessary condition: an orbit of α = (conj, z ↦ rz)
  projects onto few values in Q and in Z_n, and both quotient Haar graphs must have diameter ≤ 5; most large-k designs
  fail it.
- c8 wildcard (10..12,5): failed. A4 × PSL(2,7) at (10,5) best 9 (plain annealing 28: symmetry helps but not enough);
  A5 × Z71 with k = 5 at (12,5) best 30.
- Opus solo meanwhile: (6,8) with k = 2 (ORBIT="2 3 0"): SL(2,25) N = 15,600 solved (201 s), PSL(2,11) × Z24 N = 15,840
  solved (24 s), both VALID by build_haar2.py and apsp.c. Our record was 30,576 vertices, now 31,680. Above that:
  PSL(2,19) × Z5 (17,100) 12, PSL(2,11) × Z25 (16,500) 14, PSL(2,13) × Z15 (16,380) 12, SL(2,16) × Z4 (16,320) 15.

## 2026-10-24, table-squad round 2: k = 2 and k = 4 orbits on our Δ = 6..9, D = 7..10 records

Launched while round-1 c1–c4 finish (the k = 2 result at (6,8) is the lead). Preamble: research/squads/r2/PREAMBLE.md.
Cards: c1 (6,7) "2 3 0" · c2 (6,9) "2 3 0" · c3 (6,10) "2 3 0" · c4 (7,8) "2 3 1" · c5 (8,7) "2 4 0", "4 2 0" ·
c6 (8,8) "2 4 0", "4 2 0" · c7 (7,9) "2 3 1" · c8 wildcard: (9,8), (8,9), (7,10), (8,10) with any non-k=3 structure.
