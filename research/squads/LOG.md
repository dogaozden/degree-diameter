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

### Round 1, last reports (c1, c3, c4)
- c1 (10,5): worse than needed. Best 4 on A4 × SL(2,3) × Z7 (N 2016); SL(2,13) 6, 8, 12 (three seeds), 6 with ORBW=3;
  PSL(2,7) × Z13 8; A4 × PSL(2,7) 9; A5 × Z37 9; PGL(2,13) 26; k = 2 ("2 5 0") 34–63.
- c3 (12,5): failed. SL(2,7) × Z13 "3 4 0" 26; A5 × Z73 45; PSL(2,11) × Z7 "6 2 0" 58; PSL(2,7) × Z25 "4 3 0" 76.
- c4 (13,5): failed. S5 × Z49 and PSL(2,7) × Z35 49, A5 × Z97 54 ("3 4 1", "4 3 1"); "12 1 1" hopeless (min 234).
- Round 1 total: 0 records in 8 cards. Round 1 ran 1.5–2 h instead of 45 min for c1, c3, c4 (they did not stop on
  their own).

### Round 2, last reports (c1, c6, c7, c8)
- c1 (6,7) "2 3 0": PSL(2,11) × Z7 (N 4620) 51. c6 (8,8): "2 4 0" 7 and 11, "4 2 0" 8 and 9 on PSL(2,7) × SL(2,9)
  and SL(2,7) × PSL(2,9) (N 120,960). c7 (7,9) "2 3 1": 58, 76, 107. c8 (9,8) "2 4 1": 18–30 (150 s runs).
- Round 2 total: 0 records in 8 cards; the k = 2 idea is confined to (6,8).

### Opus, during round 3
- Exhaustive (10,5), ORBIT="3 3 1": PSL(2,7) × Z13 (63,776,075 sets): nothing below 7 uncovered. Up to automorphisms
  this group has one class of order-3 conjugation with few fixed points, so it is finished too.
- Exhaustive (10,5) on SL(2,13), ORBIT="3 3 1": 62,988,724 sets, exact minimum 6 (16 sets), no solution. Three groups
  enumerated, three floors equal to what annealing found (4, ≥ 7, 6). At D = 5 the annealer reaches the true floor of
  these orbit spaces, so (10,5) with this symmetry is closed for every group in the window that annealed to ≥ 9.
- r3-c3 (10,5) α sweeps / untried groups: SL(2,13) all 364 order-3 α have |Fix| 11, best anneal 8; A4 × Z169 12;
  S4 × Z91 26; SL(2,3) × Z91 30. Worse.
- r3-c1 (10,5) α sweep: stopped by Opus after the exhaustive result; all valid α have |Fix| 17, 71 or 287; anneals 4.
- r3-c8 wildcard: (11,5)'s 6 are two free orbits, not fixed points (ORBW=3 and 6 give energy = raw count); fixed-
  generator choices equivalent. A4-type and AGL(1,q) groups at (10,5): 9–17.
- Opus: (7,4) probe (ours 359, needs N ≥ 180, μ 42.7): plain annealing 12, k = 2 15, k = 3 30 on A5 × Z3. Dropped.

## 2026-10-24, table-squad round 4: small raises on the next rungs above our D = 7..10 records

Each card gets explicit groups just above a record, with μ at most ~1.6 above the μ the record was solved at, and the
record's own ORBIT. Preamble: research/squads/r4/PREAMBLE.md. Cards: c1 (8,9) · c2 (8,10) · c3 (7,10) · c4 (6,10) ·
c5 (9,10) · c6 (6,9) · c7 (8,8) + (8,7) · c8 wildcard (7,8), (9,8), (7,9) (no k = 3-friendly group within μ + 1.6).
Opus meanwhile: exhaustive (11,5) on A5 × Z49, ORBIT="3 3 2", one fixed-generator class (156M sets), at low priority.
- Opus: exhaustive (11,5) on A5 × Z49, ORBIT="3 3 2", fixed generator g (the choice g² is the inverse family, same
  cost): 155,906,729 sets, exact minimum 6 (504 sets), no solution. The squad's plateau at 6 was the true floor.
- r3-c7 (9,8) k = 3 next rungs: **PGL(2,16) × Z67 (N 273,360, +1.2 %) best 3** (seed 1), 6 (seed 2), 6 and 9 with two
  other α; SL(2,5)² × Z19 6; others 30–40. Closest miss of the session. Opus is running seeds 3, 4 for 900 s.
- r3-c5 (8,8): SL(2,11) × Z91 "3 2 2" (N 120,120, +0.14 %) best 6 in 240 s; PSL(2,7) × SL(2,9) with "3 2 2", "4 2 0",
  "2 4 0" under any α: 7–12. (SL(2,11) × Z91 is also on r4-c7's list.)
- r3-c2 (10,5) product groups of order 2001..2100: **AGL(1,13) × Z13 (N 2028) best 3** on three seeds (new best for
  the cell); S4 × A4 × Z7 5; SL(2,3) × A4 × Z7 4 (control); SL(2,2) × SL(2,7) 8. Opus is enumerating AGL(1,13) × Z13
  exhaustively (50.4M sets).

### Round 4 first result
- **c5 (9,10): PSL(2,149) × Z7, N = 11,577,300, ORBIT="3 3 0", solved in 8,785 evaluations (928 s): 23,154,600
  vertices** (ours 23,142,048, table 20,017,260). haarcheck_psl VALID and check_haar_indep.py VALID (ecc 10 from both
  sides, all vertices reached, 9 distinct neighbours each). Saved: research/frontier/sols/d9D10_psl_149_7_orb3f0_s1.txt,
  check table_squad/checks/d9D10_psl_149_7_orb3f0_s1.check.txt. First squad-found record of the session.
- Opus: exhaustive (10,5) on AGL(1,13) × Z13, ORBIT="3 3 1": 50,351,840 sets, exact minimum 3 (96 sets), no solution
  (AGL(1,13) is complete and has one class of order-3 elements, so this closes the group). (9,8) PGL(2,16) × Z67,
  seeds 3, 4 for 900 s each: 6 and 6 (the squad's 3 was the best of five runs).
- r4-c6 (6,9): PSL(2,11) × Z97 18 (two seeds, same plateau), SL(2,8) × Z127 46, PSL(2,7) × Z379 138. Nothing.
- r4-c8 wildcard: (9,8) SL(2,13) × Z124 (N 270,816, +0.24 %) 6, 10, 9; PSL(2,13) × Z248 13; (7,8) SL(2,7) × Z143 34.
- **c1 (8,9): PSL(2,19) × Z193, N = 660,060, ORBIT="3 2 2", solved in 310,657 evaluations (319 s): 1,320,120 vertices**
  (ours 1,316,016, table 1,091,232). build_haar2.py and haarcheck_psl VALID. The three smaller rungs before it: 9, 26,
  176 uncovered.
- c2 (8,10): SL(2,67) × Z13 (N 3,909,048) ended at 1 (a single α-fixed element). Opus ran extra seeds: **seed 12 solved
  it in 1,601 evaluations (10.8 s): 7,818,096 vertices** (ours 7,802,160, table 6,927,210). haarcheck_sl, haarcheck2 and
  check_haar_indep.py VALID. Credit: squad lead (r4-c2's group and near miss), Opus's seed.
- c3 (7,10): A5 × SL(2,8) × Z37 (N 1,118,880) ended at 3. Opus ran ten 150 s seeds (11–20): best 3, 1, 3, 1, **0**, 1, 3,
  3, 1 — **seed 15 solved it in 13,993 evaluations (40 s): 2,237,760 vertices** (ours 2,234,400, table 1,987,380).
  build_haar2.py and check_haar_indep.py VALID. Lesson: on these near misses, many short seeds beat a few long runs.
- c7 (8,8), (8,7): nothing (SL(2,11) × Z91 6 on three seeds, PGL(2,11) × Z91 7; (8,7) groups 24–774).

### Round 3, last reports (c4, c6)
- c4 (10,5) search-knob grid on A4 × SL(2,3) × Z7: all 24 runs (K 1–64, TARGP 0–100, COOL, REHEAT, RESTART) end at
  exactly 4, the enumerated floor. c6 (6,8) α sweep on A4 × PSL(2,7) × Z8: 89 valid involution α, all 8 best end at
  exactly 5. Round 3 total: 0 records; it found the best (10,5) and (9,8) leads (3 and 3) and confirmed that plateaus
  are fixed by (group, α).
- c4 (6,10): SL(2,11) × Z199 18 (one 600 s seed); other groups not reached. c3, c5: as above (stopped after the solves).
- Round 4 total so far: 4 records in 8 cards ((9,10), (8,9) found by Haikus; (8,10), (7,10) by Opus seeds on the Haikus'
  near-miss groups). c2 still running SL(2,27) × Z199 at (8,10).

## 2026-10-24, table-squad round 5: climb the ladders with many short seeds

Preamble: research/squads/r5/PREAMBLE.md (protocol: several independent short seeds per group, ORBW=3 after a seed
that ends at 1–2). Cards: c1 (9,10) SL(2,37) × Z229 … · c2 (8,10) products above 3,912,000 · c3 (8,9) PSL(2,23) × Z109 …
· c4 (7,10) SL(2,3) × SL(2,7) × Z139 … · c5 (6,10) A5² × Z73 … · c6 (9,8) many seeds on SL(2,13) × Z124 and
PGL(2,16) × Z67 · c7 (8,8) many seeds on SL(2,11) × Z91 · c8 (6,8) k = 2 rungs 16,128–16,500.

### Round 5 outcomes (all 8 Haikus stopped at ~07:30 UTC on a Haiku usage limit; the container was then suspended
and came back at 16:23 UTC with no processes; files intact)
- c1 (9,10): SL(2,37) × Z229 (N 11,591,064) **2** after one 700 s seed. c2 (8,10): A4 × SL(2,11) × Z247 27–30 (5 seeds),
  PSL(2,7)² × Z139 15–21 (5 seeds); r4-c2's SL(2,27) × Z199: 9. c3 (8,9): PSL(2,23) × Z109 6, 6. c4 (7,10):
  SL(2,3) × SL(2,7) × Z139 34–55 (bad group; its driver also lost the group list to bash's GROUPS builtin at first).
  c5 (6,10): A5² × Z73 (N 262,800) **4, 9, 4, 4**. c6 (9,8): SL(2,13) × Z124 13–14 (4 seeds, 150 s). c7 (8,8):
  SL(2,11) × Z91 and PGL(2,11) × Z91 (N 120,120) **3** in three of sixteen 90 s seeds (others 6–9). c8 (6,8): SL(2,8) × Z32
  7–12 (10 seeds of 60 s).
- Round 5 total: 0 records; near misses at (9,10) 2, (8,8) 3, (6,10) 4.
