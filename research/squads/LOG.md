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

### Round 2 outcomes (reports so far)
- c2 (6,9) "2 3 0": worse. Best 36 (SL(2,3) × SL(2,7) × Z8, N 64,512, μ 33), 68–70 on two others. Plateaus within 60 s.
- c3 (6,10) "2 3 0": worse. Best 12 (SL(2,31) × Z9, N 267,840, μ 29.5), 14–15 on PSL(2,81), PSL(2,41) × Z8.
- c4 (7,8) "2 3 1": worse. Best 13 (PSL(2,23) × Z8, N 48,576, μ 48); "2 2 3" on the same group 25.
- So k = 2 is not a general improvement on k = 3: it helped at (6,8) only, where k = 3 had just two orbits and had
  failed. Plateaus form in under a minute and do not move with reheats.

### Opus solo, between rounds
- (6,8) above 15,840 with k = 2: A4 × PSL(2,7) × Z8 (16,128) stops at 5 in 4 seeds (also RESTART=1, ORBW=2: one fixed
  point and two orbits left); SL(2,8) × Z32 (16,128) 7; PSL(2,7) × Z95 and SL(2,5)/S5 × Z133 (15,960) screen at ≥ 98.
- Inverse-closed S (new INV=1 mode, table_squad/src/haar_inv.c; makes the two odd-D conditions coincide, halving μ):
  **much worse**. (9,5) SL(2,11): 40 uncovered where k = 3 orbits solve in 0.1 s; (6,5) SL(2,5) × Z3 14; (10,5)
  SL(2,13) 20; (11,5) A5 × Z49 188. Halving μ does not pay for halving the free parameters: bipartite doubles of
  Cayley graphs are weak here.
- c5 (8,7) "2 4 0", "4 2 0": worse. Plateaus at 48–76 (≈ μ) on PSL(2,17) × Z9, A4 × PSL(2,7) × Z11, PSL(2,25) × Z3.
  On the record group SL(2,8) × Z43, random symmetric costs are ~8× higher for k = 2, f = 0 than for k = 3, f = 2.
- Opus: (8,8) on PSL(2,7) × SL(2,9) (N 120,960) "2 4 0" seeds 2, 3 with RESTART=1: 10, 8. (10,5) A4 × SL(2,3) × Z7
  with ORBW=3, seed 2: 8 (two fixed points among them).

## 2026-10-24, table-squad round 3: breadth over groups and α on the near misses, mostly (10,5)

Rounds 1–2 showed plateaus form in under a minute and depend on (group, α), so this round sweeps α (ALPHA=index) and
small product groups instead of running longer. Preamble: research/squads/r3/PREAMBLE.md.
Cards: c1 (10,5) ALPHA sweep on A4 × SL(2,3) × Z7 · c2 (10,5) other product groups of order 2001..2100 ·
c3 (10,5) ALPHA sweeps on the N = 2184 groups · c4 (10,5) search-knob grid (K, TARGP, COOL, REHEAT, RESTART) ·
c5 (8,8) N = 120,960 other structures + α sweep · c6 (6,8) α sweep at N = 16,128 · c7 (9,8) k = 3 next rungs ·
c8 wildcard (10,5)/(11,5).
- Opus: **exhaustive enumeration** (new EXHAUST=1 mode of table_squad/src/haar_inv.c). (10,5) on A4 × SL(2,3) × Z7 with
  ORBIT="3 3 1", default α: all 49,013,160 symmetric S evaluated (2 × 590 s); none of cost 0, the exact minimum is
  4 (72 sets). So the annealer had found the floor. Up to automorphisms of G every other order-3 α of this group fixes
  ≥ 71 elements, so the group is finished for this structure. Told r3-c1 to stop its α sweep, and r3-c3 to move from
  α sweeps (one α class each for PSL(2,7) × Z13 and SL(2,13)) to untried groups. Output:
  table_squad/exhaust/d10D5_prod_psl_3_sl_3_7_orb331.txt.
