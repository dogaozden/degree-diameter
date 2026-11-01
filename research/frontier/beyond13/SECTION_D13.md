### D = 13 at Δ = 3..10 and D = 14 at Δ = 3..8 (job beyond-d13, 2026-11-01)

Job beyond-d13 (Opus director + four Haiku squad rounds of 16 cards, cloud session, branch
claude/beyond-d13-search-z35z61). Fourteen new cells (nothing was recorded at D = 13, 14 before), and two D = 11 values
raised. Size limit: at most about 20 billion vertices. Files: research/frontier/beyond13/ (cells.txt, cells_other.txt,
rows13.py for the rows; sols/, runs/ (haarcheck_gen logs), checks/ (apsp, metacheck), graphs/ (edge lists),
THEORY.md); squad cards and scoreboards research/squads/beyond13/r1..r4; log research/squads/LOG.md.

**What won where.**
- Δ = 3 (both D): cyclic voltage lifts of the Desargues graph GP(10,3), annealed voltages (squad r2/e16's lift.c):
  Z160 at D = 13 (3,200), Z280 at D = 14 (5,600, director). Better than every Haar graph tried (A6 x Z4 2,880 by
  exhaustive pairs at D = 13; PSL(2,7) x Z15 5,040 at D = 14). Why (r3/f03, THEORY.md section 2): in a Z_n lift a walk's
  end depends only on its net traversal vector; GP(10,3) (girth 6, Betti number 11) keeps 82 % of the 24,574
  nonbacktracking walks of length <= 13 distinct.
- Δ = 4, 5 at odd D, and Δ = 4 at D = 14: Haar graphs of odd-order groups with random S: Frobenius groups
  Z_m x|_r Z_k (m prime, k odd) and products of two (haar_gen3, or the director's bit-parallel hmeta). Reason
  (THEORY.md section 1): at odd D the hard holes are involutions and central elements (ODD_D_HOLES.md); a Frobenius
  group has neither. The same rule raised (4,11) from 24,360 to 27,554 and (5,11) from 297,648 to 299,222. Small k
  fails (nearly abelian: random-S word cover 1 % for k = 1, 6 % for k = 3, 97-99 % for k >= 11; r2/e11).
- Δ = 5 at D = 14: PSL(2,53) x Z83 with random S. The orbit form "3 1 2" (one random fixed generator + one orbit)
  stalls at Δ = 5 (cost 18 where random S solves in seconds).
- Δ = 6..10: SL/PSL(2,p) x Z_n with alpha-orbit S (haar_big0). At D = 13, SL with small n (as at D = 11) and also PSL
  with moderate n (40-75) solved; r1/c14's anatomy at (5,13): -I is missed by 20-46 % of random S, SL has 16-20 holes per
  random S against 22-27 for PSL.
- (10,13) is at the 20-billion cap (PSL(2,503) x Z157, the first S solved, λ = W/N = 31.8).
- Even D was again easy: (8,14) solved at mu 7.1 in 21 evaluations; odd D needed chained links at mu 7-9.

**Squad (64 Haiku cards in 4 rounds of 16; LOG.md).** The two ideas that moved small Δ came from wildcard cards:
odd-order groups (r1/c15) and voltage lifts (r2/e16); a prime-power field (PSL(2,49), r1/c16) and random S at Δ = 5
(r1/c08) were also card ideas. The mid cells (Δ = 6, 7) were raised 1-5 % by cards in every round. The director's
contributions: the cell plan and selection, the (8,13), (8,14), (9,13), (10,13) values, the Δ = 3 D = 14 lift, the
checkers for non-SL/PSL graphs (metacheck.py, metacheck2.py, tab2edges.py, meta2edges.py), hmeta and liftd, THEORY.md.

**What failed or was not tried.**
- Orbit S inside metacyclic groups (alpha = scaling): costs saturate (r2/e03, e14, director). Metacyclic groups at
  even D: no gain (r2/e06), except (4,14) where Z7001 x|_4532 Z35 (odd order) beat PSL(2,41) x Z7 by 1.6 %.
- Lifts at Δ = 4, 5: K4,4, PG(2,3), GQ(3,3), the biplane and random bases stayed below the Haar values (best PG(2,3) x
  Z4600 = 119,600 at (4,13)); THEORY.md Fact 2 caps K4,4 lifts. Non-abelian voltage groups on GP(10,3): cost 2 at 3,300.
- Near misses at cost 1-2 that did not close: (3,14) GP(10,3) x Z282 and Pappus x Z312; (3,13) Z33 x|_4 Z5 voltages;
  (4,13) Z3307 x|_265 Z29 and Z2297 x|_1862 Z41 (N ~ 94-96k); (6,13) SL(2,59) x Z103; (8,14) PSL(2,397) x Z181 (mu 12).
- The machine (4 cores) was the limit: the director's three big checks held 4-5 threads, so cards ran at 5-10 % of a
  core (r1/c01, c02, r2/e04, e13 found nothing for that reason). The (10,13) check was OOM-killed once after 58 min
  (a card's numpy checker plus a director search pushed the box over 15 GB) and was rerun.
- Not tried: (9,13) above mu 3 (one SL group solved in 5 evaluations; a push would gain ~3 % and need another
  two-hour check), (8,14) above mu 7.1.
