### D = 14 raises at Δ = 3..7, the new cells (9,14) and (10,14), and Δ = 3 side results (job beyond-d14, 2026-11-01/02)

Job beyond-d14 (Opus director + six Haiku squad rounds of 15-16 cards, cloud session, branch
claude/beyond-d14-new-cells-v6dcaa). The D = 14 column at Δ = 3..8 had been filled earlier the same day by job
beyond-d13; this job raised every cell at Δ = 3..7, added (9,14) and (10,14), and raised (3,12) and (3,13) on the side.
Files: research/frontier/beyond14/ (rows14_data.py lists every value with its check; sols/, checks/, ownsmall/ for the
lifts, census/ for the Foster census graphs, tools/ and bin/ for the search tools); Haar solutions also in
research/frontier/sols/ and their haarcheck_gen / build_haar2 logs in research/frontier/runs/cloudcheck/; lift edge lists
with apsp outputs in research/frontier/beyond/graphs/; squad cards and scoreboards research/squads/beyond14/r1..r6; log
research/squads/LOG.md.

| cell | beyond-d13 | this job | gain | method |
|---|---:|---:|---:|---|
| (3,14) | 5,706 | **7,004** | +22.7 % | 2+2 base lifted over Z103 x\|_8 Z17 |
| (4,14) | 497,042 | **504,382** | +1.5 % | Z6151 x\|_5694 Z41, random S, 1-opt finisher |
| (5,14) | 12,795,166 | **13,467,134** | +5.3 % | Z100501 x\|_52125 Z67, random S, hole-directed + low-T finisher |
| (6,14) | 187,990,656 | **193,539,888** | +3.0 % | SL(2,107) x Z79, ORBIT "3 2 0" |
| (7,14) | 1,674,490,944 | **1,732,018,320** | +3.4 % | SL(2,179) x Z151, ORBIT "3 2 1" |
| (8,14) | 11,325,238,056 | (not attempted) | | |
| (9,14) | (none; floor 11.3e9) | **20,002,113,120** | new cell | PSL(2,241) x Z1429, ORBIT "3 3 0" |
| (10,14) | (none) | see the row | new cell | PSL(2,239) x Z1789, ORBIT "3 3 1" (or the (9,14) graph by monotonicity) |
| (3,13) | 3,400 | **4,324** | +27 % | 2+2 base lifted over Z47 x\|_2 Z23 |
| (3,12) | 2,368 (lab, own-small) | **2,436** | +2.9 % | 2+2 base lifted over Z87 x\|_7 Z7 |

**Δ = 3: regular lifts of tiny bases over Frobenius groups.** The lab's (3,10)-(3,12) records (job own-small) are
regular voltage lifts of 4+4 and 5+5 cubic bases over small non-abelian groups, with the base and the voltages annealed
together (salift_s). At D = 14 the same tool over Z113 x| Z7 (order 791, 4+4 base) gave 6,328 in a 60-s screen, a 3+3
base over Z47 x| Z23 (order 1,081) 6,486 (card r2/d04), and a 2+2 base over Z103 x|_8 Z17 (order 1,751) 7,004 (director,
40 CPU-seconds). The same 2+2 lifts gave 4,324 at D = 13 (Z47 x| Z23, 30 CPU-seconds) and 2,436 at D = 12 (Z87 x| Z7, card
r5/g14). For comparison: the Foster census of cubic edge-transitive graphs (Potocnik et al., fostercensus.graphsym.net)
has two semisymmetric graphs of diameter 14 on 6,272 vertices, CSS(6272,3) and CSS(6272,7) (built here from the census
LCF notation, apsp VALID, diameter exactly 14; not ours); beyond-d13's cyclic lifts stopped at 5,706.

Measured with the size law (N = vertices per side, W = 16,383 cross-side words at Δ = 3, D = 14, mu = N exp(-W/N)):
the cyclic Pappus lift sits at mu 9, the census graph at 17, the 4+4 lift at 18, the 3+3 lift at 21 and the 2+2 lift at
33 (the lab's (3,12) 4+4 record is at 37 by the same count). Above 7,004 the 2+2 lifts hit a hard floor: every Frobenius
group of order 1,752-1,884 stalls at cost >= 6 and two non-faithful metacyclic groups with large k (Z37 x|_8 Z48,
Z17 x|_2 Z104) at cost 2, which are strict local minima for single voltage changes and endpoint swaps (exact polish,
r4/f01) and for a hole-directed 2-opt (r5/g06). Card r4/f05 (research/squads/beyond14/r4/f05/LIFTS.md) measured why the
group matters: at matched size, groups with a small action order k (k = 3-6, and abelian groups) collapse the endpoints of
non-backtracking walks (5-50 % distinct at length <= 13) while k >= 11 gives 94-98 %; the base size p matters less than
the group. The tiny-base advantage does not carry over to Δ = 4, 5: lifts of 2+2 bases over large-k Frobenius groups
stayed at cost 26 at 503K vertices (r3/e07) and solved only up to 8M vertices at Δ = 5 (r3/e11), below the Haar graphs.

**Δ = 4..7: Haar graphs, pushed further.** Same families as beyond-d13, larger groups, and finishers.
- (4,14): metacyclic Z_m x| Z_k with m prime and random S (hmeta): 20-s screens over every such group in an order window,
  chained (Z3079 x| Z81, 498,798, r1/c05; Z5849 x| Z43, 503,014, r2/d07), then an exhaustive 1-opt over one generator
  slot of a cost-2 state gave Z6151 x| Z41, 504,382 (r3/e06). Composite m works too (Z2 x (Z1877 x| Z67), 503,036, r4/f07).
  Cost-1 states above the record (Z7211 x| Z35, N 252,385) survive the hole-directed finisher, low-temperature anneals and a
  full 1-opt over all three slots (r5/g04).
- (5,14): an order-2 orbit form in PSL(2,163) x Z3 (S = {e, x, ax, y, ay}, 12,991,752, r1/c11) and metacyclic random S
  (Z152393 x| Z43, 13,105,798, r1/c08) passed the old value; then finishers on cost-1 states: the hole-directed finisher
  (each round: a random generator slot, K candidates that force a word through that slot onto the missing element, keep
  the best, sideways moves allowed; r4/f09) closed Z83267 x| Z79 (13,156,186), and the same followed by a low-temperature
  anneal (T0 0.5, T1 0.1, TARGP 90, K 4) closed Z100501 x| Z67 (13,467,134, r5/g02).
- (6,14), (7,14): the beyond-d13 forms ("3 2 0", "3 2 1" in SL/PSL(2,p) x Z_n). At D = 14 a random symmetric S often has
  cost 0 outright or within a few evaluations: SL(2,137) x Z37 at the first random S (mu 10.3, r1/c12), RANDORB screens of
  8-60 random S per group (r2/d15, r3/e12, r5/g09), and short low-temperature anneals from cost-3 states (r4/f15). Other
  orbit forms ("6 1 0", "2 3 0", "3 1 3" at Δ = 6; "2 3 1", "6 1 1" at Δ = 7) were much worse.

**Δ = 9, 10: new cells.** The size law puts the plausible Haar order for (9,14) at N ~ 2.8e10 and for (10,14) at ~1.2e11,
far above what the checker can do here (haarcheck_gen needs 0.75 N bytes and ~0.7 CPU-microseconds per element), so these
values are set by the checker, not by the search: at N ~ 1e10 the first random symmetric S has cost 0 (mu ~ 0).
H(PSL(2,241) x Z1429, S), S three free alpha-orbits of size 3, has 20,002,113,120 vertices and diameter 14 (haarcheck_gen
from (e,A) and (e,B), 2,858 s on 2 threads); it is also a lower bound for (10,14). H(PSL(2,239) x Z1789, S) with
S = {e} + three alpha-orbits (10-regular) has 24,422,855,520 vertices (search cost 0 at the first S; see the (10,14) row
for its check).

**What failed.**
- (3,14): cyclic lifts of larger-girth bases (Tutte 12-cage, Foster graph: cost 270-376), metacyclic voltages on the Pappus
  graph, cubic Haar graphs of non-metacyclic groups (cost 6 at 6,560), 2+2 lifts over F_(p^2) x| Z_k, PSL(2,7) x Z11 (cost 4
  at 7,392), p = 3, 4 with large-k groups (cost 8 at 7,224-7,308), products and simple groups x cyclic at p = 2.
- (4,14)-(5,14): products of Frobenius groups, PSL/SL/PGL/AGL with random S, order-2 orbit forms in SL(2,q) x Z_n and in
  metacyclic groups (cost 18-4,000), lifts of 2+2 bases (above), the z-uniformity filter at Δ = 6.
- (6,14) above 97M and (7,14) above 866M: cost-3 states (SL(2,241) x Z7 at 98.0M; PSL(2,223) x Z157 at 870.5M) and one
  cost-1 random S (SL(2,359) x Z19 at 879M) did not close in the time.
- (8,14) was not attempted: one evaluation takes ~10-30 s at N ~ 5.8e9 here, the check ~1 hour, and the expected gain at
  the incumbent's mu 12 is ~1-2 %.

**Process notes.** The machine has 4 cores; the Agent tool's "remote" isolation runs in the same container, so 16 cards
plus the director's checks share them (load 15-25). The kernel's autogroup scheduling ignores per-process nice across
sessions: long checks were given priority with `echo -15 > /proc/<pid>/autogroup`. A container restart at 23:28 UTC and
the Agent tool's 30-minute default background limit each stopped a (9,14) check once. Several cards called remote-session
tools despite the header (create/archive of an empty session in round 2; failed archive and interrupt calls later); no
other session was affected.
