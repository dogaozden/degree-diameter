# table-squad: Opus plus a squad of 8 Haikus on the bipartite (Δ, D) table

Job "table-squad", 2026-10-24, one Opus cloud session (4 cores, 15 GB, shared with the squad). Branch
`claude/degree-diameter-table-squad-0xgp3g`. Every round is logged in `LOG.md`; the cards and the squad's raw files are
in `r1/`, `r2/`, …; my own runs, logs and check files are in `table_squad/`.

## What I aimed at, and why

The table (research/frontier/TABLE.md) splits into three kinds of cells:

- D = 3, 4, 6: Moore graphs or our own algebraic constructions (Theorems A, C1, D, R). Nothing quick to gain.
- D = 7..10, Δ ≥ 6: Haar graphs, raised many times by the orbit search (research/structured). Other sessions are on the
  big cells (Δ ≥ 10), so I took the Δ = 6..9 cells there.
- **D = 5, Δ = 6 and 10..15**: we hold nothing. The theorem search showed that these table values are polygon covers,
  (2j+1)·|GQ(q)| with Δ = q+1+j. Earlier Haar searches at D = 5 (research/d5) used random connection sets only and
  stopped 2–6 elements short at Δ = 6 and 10. The orbit search, which is what raised D = 7..10, had never been run at
  D = 5.

Calibration before the first squad: at (9,5) on SL(2,11) (N = 1320), `haar_sym` with S = three conjugation orbits of
size 3 solved in 0.1 s, where plain annealing stalls at 2 uncovered after 12M evaluations. So the D = 5 column was the
first squad's target.

Two lessons from the calibration, written into the squad's preamble (r1/PREAMBLE.md):
1. At D = 5 the binding cost is the α-fixed points: each costs about e^(−λ/k) expected misses with λ = W/N ≈ 3.5,
   against e^(−λ) for a free element. Groups need automorphisms with almost no fixed points (n = 1, or a cyclic factor
   whose primes are 1 mod k).
2. "Nearly abelian" groups fail with orbit symmetry: metacyclic and Heisenberg scalings left 924 and 78 uncovered.

## Results so far

| cell | before (ours / table) | new | group, structure | check |
|---|---|---|---|---|
| (9,10) | 23,142,048 / 20,017,260 | **23,154,600** | PSL(2,149) × Z7, ORBIT="3 3 0"; squad-r4-c5 | haarcheck_psl and check_haar_indep.py VALID (table_squad/checks/d9D10_psl_149_7_orb3f0_s1.check.txt) |
| (8,10) | 7,802,160 / 6,927,210 | **7,818,096** | SL(2,67) × Z13, ORBIT="3 2 2"; r4-c2's group and near miss (1 left), Opus's seed 12 | haarcheck_sl, haarcheck2, check_haar_indep.py VALID (d8D10_sl_67_13_orb3_s12.check.txt) |
| (7,10) | 2,234,400 / 1,987,380 | **2,237,760** | A5 × SL(2,8) × Z37, ORBIT="3 2 1"; r4-c3's group (3 left), Opus's ten-seed sweep, seed 15 | build_haar2.py, check_haar_indep.py VALID (d7D10_prod_psl_5_sl_8_37_orb3_s15.check.txt) |
| (8,9) | 1,316,016 / 1,091,232 | **1,326,960** | SL(2,19) × Z97, ORBIT="3 2 2" with ORBW=3; Opus seed sweep. Rungs on the way: 1,320,120 PSL(2,19) × Z193 (squad-r4-c1), 1,323,696 PSL(2,23) × Z109 (squad-r6-c5) | build_haar2.py, haarcheck_sl, haarcheck2 VALID (d8D9_sl_19_97_orb3_s2.check.txt; the two rungs: d8D9_psl_19_193_orb3_s1, d8D9_psl_23_109_orb3_s3) |
| (6,8) | 30,576 / 29,790 | **31,680** | PSL(2,11) × Z24, S = 3 orbits of size 2 under conjugation (ORBIT="2 3 0"), Opus solo; first rung 31,200 on SL(2,25) | build_haar2.py VALID; apsp.c all-pairs diameter 8 (table_squad/checks/d6D8_psl_11_24_orb2f0_s1.check.txt, d6D8_sl_25_1_orb2f0_s1.check.txt) |

(6,8) had resisted the orbit search with k = 3: with Δ = 6 that leaves only two orbits, and STRUCTURE.md §8 found no
symmetric solution at all at N ≈ 15,500. With k = 2 there are three orbits (a much larger space), and at D = 8 a fixed
point costs only e^(−λ/2) ≈ 0.04, so the price of the symmetry is small. SL(2,25) solved in 201 s, PSL(2,11) × Z24 in
24 s. Above that the rungs stall: 16,128 (two groups) at 5 and 7, 16,320–17,100 at 12–15.

## What did not work (all logged in LOG.md)

- **The D = 5 column (round 1, 8 Haikus).** No cell fell. (10,5) came closest: 4 uncovered on A4 × SL(2,3) × Z7
  (N = 2016), 6 on SL(2,13). (11,5) sits at exactly 6 on A5 × Z49 in every run. (12,5) 26, (13,5) 49, (14,5), (15,5)
  hundreds. (6,5): the symmetric families are small enough to sample exhaustively and their minima are 16–24, worse
  than the non-symmetric searches of research/d5. The squad's two useful findings: the minimum over random symmetric
  samples predicts where annealing stops, and (c7) every orbit projects onto few values in the quotients Q and Z_n,
  whose Haar graphs must also have diameter ≤ D, which rules out most designs with large k.
- **k = 2 and k = 4 elsewhere (round 2).** k = 2 helped only at (6,8). At (6,7), (6,9), (6,10), (7,8), (7,9), (8,7),
  (8,8), (9,8) it plateaus at 7–76 uncovered, above what k = 3 reaches.
- **Inverse-closed S** (Opus, a new INV=1 mode in table_squad/src/haar_inv.c). At odd D a Haar graph must cover G
  twice, by (S⁻¹S)^j and by (SS⁻¹)^j. If S = S⁻¹, swapping the two sides is an automorphism, so the two conditions
  coincide and μ halves. It is much worse anyway: (9,5) on SL(2,11) stalls at 40 where k = 3 orbits solve in 0.1 s.
  Halving the free parameters costs more than halving μ gains; bipartite doubles of Cayley graphs are weak here.
- **Annealing plateaus are properties of (group, α).** They form within a minute and survive reheats, restarts and
  ORBW. This is why round 3 sweeps α and groups instead of running longer, and why I added an exhaustive mode.

## Exhaustive enumeration (Opus)

Because the D = 5 orbit spaces are small, I added an exhaustive mode to my copy of haar_sym (`EXHAUST=1`,
table_squad/src/haar_inv.c): it evaluates every S = {e} ∪ (fixed generators) ∪ (m distinct α-orbits). Validated on
(9,5) SL(2,11), where it finds solutions in 1/40 of the space. Results (outputs in table_squad/exhaust/):

| cell | group, ORBIT | sets | exact minimum | annealing had found |
|---|---|---|---|---|
| (10,5) | A4 × SL(2,3) × Z7, "3 3 1" | 49.0M | 4 (72 sets) | 4 |
| (10,5) | PSL(2,7) × Z13, "3 3 1" | 63.8M | ≥ 7 | 8 |
| (10,5) | SL(2,13), "3 3 1" | 63.0M | 6 (16 sets) | 6 |
| (11,5) | A5 × Z49, "3 3 2" | 155.9M | 6 (504 sets) | 6 |

Two conclusions. First, at this size the annealer finds the true floor of the orbit space, so a plateau is a property
of (group, α), not of effort. Second, up to automorphisms of G each of these groups has only one class of order-3
conjugation with few fixed points, so each line above closes that group for that structure. Under three-orbit
symmetry, (10,5) and (11,5) would need a different group, and in their order windows the remaining candidates all
anneal to 8 or more.

Why some groups are so much better than others: the Poisson model predicts about 0.03 symmetric solutions for SL(2,11)
at (9,5), and enumeration finds about 100 (3 in 1/40 of the space). For A4 × SL(2,3) × Z7 at (10,5) the model predicts
about 3·10⁻⁵ and there are none. This fits quasirandomness: SL(2,q) has no nontrivial representation of dimension
below (q−1)/2, so product sets such as (S⁻¹S)² spread over the group faster than random sets (Gowers), while groups with
abelian quotients (a Z_n factor, A4, PGL) have 1-dimensional representations. At D = 5, where words are short, this
decides everything. The perfect groups in the (10,5)–(13,5) order windows are SL(2,13) only (now enumerated), so the
D = 5 column is out of reach for orbit-symmetric Haar graphs.

## Squad rounds

(details and per-card numbers in LOG.md; cards and preambles in r1/ … r6/)

| round | aim (Opus) | records | what the squad added |
|---|---|---|---|
| 1 | D = 5 column, orbit search, one cell per card | 0 / 8 | the random-sample minimum predicts the plateau; quotient condition on orbits (c7); (6,5) symmetric families sampled exhaustively (minima 16–24); (11,5) floor 6, (10,5) 4 |
| 2 | k = 2 and k = 4 orbits on Δ = 6..9, D = 7..10 | 0 / 8 | k = 2 does not transfer beyond (6,8); near misses (8,8) 7, (9,8) 18 |
| 3 | α and group breadth on the near misses | 0 / 8 | new leads: (10,5) AGL(1,13) × Z13 at 3, (9,8) PGL(2,16) × Z67 at 3, (8,8) SL(2,11) × Z91 at 6; knob grid and α sweeps showed plateaus are fixed by (group, α) |
| 4 | explicit next-rung groups above each record, the record's own structure | **4** | (9,10) and (8,9) solved by Haikus; (8,10) and (7,10) near misses (1 and 3 left) that Opus converted with extra seeds |
| 5 | the same ladders with many short seeds | 0 / 8 | stopped early by a Haiku usage limit; near misses (9,10) 2, (8,8) 3, (6,10) 4 |
| 6 | new seeds on the round-5 near misses | **1** | (8,9) 1,323,696 by c5 in 33 s; elsewhere floors of 2–6 over 12–16 seeds per group |

Opus alone in this session: the (6,8) record (k = 2 idea and both rungs), the exhaustive mode and its five closed
groups, the inverse-closed negative result, the choice of every card's cells, groups and protocol, and all checking.

## Did the squad help? (honest account so far)

- **Exploration cards did not pay.** Rounds 1–3 gave each Haiku a direction ("screen this window", "sweep α", "try
  anything plausible"). 24 cards produced no record. The Haikus executed carefully and reported honestly, and a few of
  their observations were useful (the quotient condition, the plateau-predicts-floor rule, two new near-miss groups),
  but none proposed an idea that changed the plan. The fixed costs were real: three round-1 cards ran 1.5–2 h instead
  of 45 min, several stopped without reporting until pinged, and `pkill -f` patterns killed their own shells.
- **Execution cards paid.** Round 4 gave each Haiku an explicit, ordered list of groups (computed by Opus from μ and
  the record's structure) and a fixed protocol. 8 cards gave 4 records, 2 directly and 2 through near misses that more
  seeds converted. The machine has 4 cores either way, so the squad's advantage was not extra compute but parallel
  bookkeeping: eight cells driven, logged and checked at once while Opus worked on something else.
- **What Opus did that the squad could not:** spot that (6,8) needed k = 2; write the exhaustive mode and prove the
  D = 5 plateaus are true floors; work out the α classes (which made two Haiku sweeps redundant); compute the rung
  lists; diagnose a residual of 1 as a fixed point (ORBW); and notice that solve times are heavy-tailed.
- Overall: 5 cells raised this session, with 8 record graphs ((6,8) ×2 rungs, (7,10), (8,9) ×3 rungs, (8,10), (9,10)). Haikus found
  3 of the 8 record graphs directly ((9,10), two (8,9) rungs), and their near-miss groups led to 2 more ((8,10),
  (7,10)); Opus found both (6,8) graphs and the last (8,9) rung alone. The combination beat what I would have done alone in rounds 4
  and 6, when the Haikus ran explicit lists. A fair summary: Opus aims and verifies; Haikus are good parallel hands for
  well-specified runs and poor explorers.
- Practical lessons for the next squad session: give each card an explicit list and a stopping rule; have every card
  run one driver script under nohup (fewer tool calls, which also matters because round 5 hit a Haiku usage limit);
  never use `pkill -f` (it matches the caller's own shell); ask for the report before the budget ends, because several
  Haikus handed back late or only after a reminder.
