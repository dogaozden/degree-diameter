# big-squad-4-8: one Opus director with a large Haiku squad

Job "big-squad-4-8", 2026-10-26, one Opus session (session_01QhUN8cKzD3kdiZv1fBP88r, branch
claude/bipartite-4-8-squad-zmk3qt), cloud container with 4 cores and 15 GB. Doğa's question: does one Opus director
with ~48 Haikus per round do better than the usual Opus + 8 Haikus? Goal: beat the bipartite (4,8) record (2,184), then
(4,9) (4,970), (3,9) (506) and (3,10) (800) if (4,8) looked exhausted.

## Answer

**No record.** 119 Haiku cards in 5 rounds (13.7 Haiku-hours of wall time, 04:28-05:58 UTC) plus the director's own
work (to 06:40 UTC) found no valid graph above any of the four table values. Results per Haiku-hour: 0 records,
20 kept findings, about 1.5 per Haiku-hour (section 1).

The earlier Opus + 8-Haiku squads did find records (exp2-squad: three D = 7 cells; d12D7: the (12,7) record via a hub
group from a squad card), but in cells where a construction had headroom. The four cells here sit at or just above what
the natural algebraic families can reach (below), so the record count does not separate "48" from "8". What the round
data do show:

- **Breadth was real.** 48 distinct directions were run and scored within 30 minutes; 107 cards covered four cells in
  80 minutes. An 8-card squad would have needed about six rounds for the same coverage.
- **Depth was shallow and compute was diluted.** Median card length 6-8 minutes (the time box was 25); 20 concurrent
  Haikus on 4 cores put the load at 10-19, so a "60 s search" got roughly 10-20 s of CPU. Several cards reported "longer
  runs did not help", partly an artefact of this.
- **Duplication.** In round 1, seven cards independently fell into the same trap (Z_55 x|_2 Z_20 at cost 1).
- **The decisive steps came from the director**, not from breadth: new tools (haar_tab, flift, exh_meta.py) and
  exhaustive searches showing that the annealing floors are true minima, ending in a certificate that no metacyclic Haar
  graph of order 1,093..1,130 (89 groups) beats 2,184 (section 3).
- **Haiku cards that mattered**: c31 (surgery on the valid seed, the lowest-miss near miss), c01 (the trap is local),
  b01 (31 valid 2,184 seeds, apparently one graph), a01 (all root variants of the best new group are isomorphic), d16
  (the central involution behind the (4,9) cost-4 floor), h01-h03 (finished an earlier session's exhaustive (3,10) scan
  in ten minutes each, and found a new cost-2 near miss at n = 880), e01 (exhaustive certificates for five groups).

Recommendation: on cells like these, a big squad is a fast way to map the negative space, not to find records. Fewer,
deeper cards (16-20 per round, each with about twice the CPU, and an explicit "already found" list to avoid duplicates),
plus the director's exhaustive checks, would have given the same coverage at lower cost. The concurrency cap of 20
subagents means 48 cards per round already run as a rolling queue of 20.

## 1. Rounds

Kept findings (used by a later round or the report): c01, c31, c07, c18 (round 1); b01, b02/b05/b08, a01, a06, a12
(round 2); d16, e01 (round 3); h01, h02, h03, h04, h08 (round 4); k03, k06 (round 5): 20 of 119 cards (17%), about 1.5 per
Haiku-hour.

| round | cell(s) | cards | Haiku-minutes | median card | best verified result | kept for the next round |
|---|---|---|---|---|---|---|
| 1 | (4,8) | 48 | 318 | 6.2 min | n = 2,186 with 247 far pairs (surgery, c31); n = 2,200 cost 1 (Haar, Z_55 x|_2 Z_20) | surgery; abelian-by-cyclic groups |
| 2 | (4,8) | 26 | 178 | 7.1 min | n = 2,186 with 217 far pairs (b08) | (4,8) looks closed: move to (4,9) |
| 3 | (4,9), 4 cards (4,8) | 20 | 165 | 8.1 min | n = 4,992 cost 4 (meta 104 24 7) | move to the cubic cells |
| 4 | (3,10), (3,9), 2 cards (4,9) | 13 | 87 | 6.3 min | (3,10): n = 880 cost 2 (new, 2+2 lift of Z_11 x| Z_20) | untried cubic families |
| 5 | (3,10), (3,9) | 12 | 75 | 6.4 min | no improvement: (3,10) bi-Cayley/loops/semi-edges >= 5, non-bipartite bases >= 8; 3+3 certified (minima 2, 8, 12) | stop (two rounds without progress) |

Every round is logged in research/squads/LOG.md (cards in one line each, best score per card, what was kept). Cards,
headers, scoreboards and each card's work folder are in research/squads/b48/r1..r5/.

## 2. Best near misses per cell (all re-scored by the director with score48)

| cell | table | best near miss | file |
|---|---|---|---|
| (4,8) | 2,184 | n = 2,186, 217 far pairs (all at distance 9): valid 2,184 seed, 4 edges deleted, 2 vertices added | b48/r2/b08/run3_k4_noxy.edges |
| (4,8) | 2,184 | n = 2,200, 1,100 far pairs (Haar graph of Z_55 x|_2 Z_20; proved optimal for that group) | b48/r1/c01/best_cost1_n2200.edges |
| (4,9) | 4,970 | n = 4,992, 4,992 far pairs (Haar graph of meta 104 24 7) | b48/r3/d16/lift104.edges |
| (3,10) | 800 | n = 816, 136 far pairs (3+3 lift of Z_17 x| Z_8; known from an earlier session) | b48/r4/h04/push_17_8_4_b0.out.edges |
| (3,10) | 800 | n = 880, 220 far pairs (2+2 lift of meta 11 20 3; new; exhaustively minimal for that group) | b48/r4/h03/res/best220.edges |
| (3,9) | 506 | n = 544, 1,088 far pairs (2+2 lift of Z_17 x| Z_8) | b48/r4/h08/best136.edges |

## 3. Negative results that are proofs (exhaustive, up to isomorphism)

Haar graph H(G, S) of a metacyclic group Z_m x|_r Z_k with r - 1 a unit mod m: up to isomorphism, S = {e, x, y, z} with x
an orbit representative of the automorphisms (a, j) -> (u a + c [j], j), [j] = (r^j - 1)/(r - 1) (tools/exh_meta.py),
and all pairs {y, z}; every set scored with flift (~540k sets/s at D = 8).

- (4,8): Z_91 x|_25 Z_12 (order 1,092) reaches 0 (the table value 2,184; sanity check). Z_55 x|_2 Z_20 (1,100):
  minimum lift-cost 2, i.e. no Haar graph of it has diameter 8; the annealing floor seen by 9 cards is the true minimum.
  e01 (round 3) certified five more groups of order ~1,100 (four exact minima 8, 14, 17, 34 and one bound >= 3), each
  equal to its annealing floor.
- **(4,8), all metacyclic groups of order 1,093..1,130** (r != 1, r - 1 a unit mod m, one r per cyclic subgroup <r>;
  89 groups): none has a Haar graph of diameter 8. 77 by exhaustive search (minimum lift-cost >= 2 in every group; the
  smallest minima are 2, 3, 4 and 6 for four groups of order 1,100, then 8 for Z_137 x|_10 Z_8 at 1,096), and 12 (m = 3, 5,
  so k > 216) by the quotient bound below. Table: research/squads/b48/cert_4_8_meta_1093_1130.tsv; driver
  tools/cert_meta_one.sh (minima above 2 are lower bounds because counting stops at LIMIT = 2; 0 would have been exact).
- **Quotient bound (4,8)** (director, 06:20 UTC): in an abelian Haar graph with S = {0, s_1, s_2, s_3}, the other side
  within distance 7 holds at most 216 values (coefficient vectors c with sum 1 and sum |c_i| <= 7) and the same side
  within distance 8 at most 309. Distances do not grow in a quotient, so **no group with an abelian quotient of order
  > 216 has a (4,8) Haar graph**. In particular no abelian group, and no Z_m x| Z_k with k > 216, works above 2,184.
- (4,9): Z_101 x|_5 Z_25 (order 2,525, n = 5,050): minimum lift-cost 2 over all 79.5 million sets.
- (3,10): exhaustive 2+2 cubic lift scans (all voltage assignments) over 38 non-abelian groups of order 208, 25 of orders
  210..216 and 59 of orders 217..230 (h01-h03): minima 14, 6 and 2. With the earlier session's complete scan of orders
  201..207 (minimum 2), no 2+2 cubic lift of these groups has diameter 10 at n = 804..920.
- (3,10), 3+3 bases: meta 17 8 4 minimum 2 (confirms the earlier proof), meta 7 20 6 minimum 8, meta 9 16 8 minimum 12
  (k06); bi-Cayley graphs with loops over all 739 metacyclic groups of order 401..460 with even k: minimum 6 (k03).
- (3,9): exhaustive 2+2 cubic lift scans over 91 groups of orders 127..140 (h08): minimum 16; 3+3 with meta 15 6 4: >= 14 (k10).

## 4. Director's tools (research/squads/b48/tools/)

score48 (edge-list scorer, any d and D), farlist, edgecrit (damage of deleting one edge), lift (voltage-lift annealer
over any group table; batch eval; loops, semi-edges, parity option ODDSTRIDE), flift (bit-parallel lifts of bipartite
bases, ~15x faster than lift), haar_tab (haar_fast with any group table), groups.py, abc.py (split abelian-by-cyclic
groups M x| Z_k with M a sum of finite fields; metacyclic is the case f = 1), exh_meta.py.

## 5. Observations for the lab

- **The four cells sit at the top of the natural families.** 2,184 = 2 x 1,092 is a Haar graph of Z_91 x|_25 Z_12 (the
  only order-1,092 group found with cost 0, and apparently a single graph); 4,970 = 2 x (71 x 35) matches a Haar graph of
  the Frobenius group Z_71 x| Z_35. Just above these orders every group tried has a positive floor, and the floors are
  true minima where we could check exhaustively.
- **Floors are structural, not search failures.** Cost 1 at order 1,100: one B-side element reached only at distance 9;
  cost 4 at (4,9) order 2,496: the central involution (52, 0) is far in every optimum; (3,10) cost 2: one orbit of far
  pairs at distance 11.
- **Surgery** (delete k edges of a valid seed, add 2 vertices) floors near 217 far pairs at (4,8): every edge of the
  vertex-transitive seed is critical for 165-180 pairs.
- **Weak families** (round 1-5 evidence): abelian lifts, lifts of Moore/girth-6/8 bases, Cayley graphs, coset graphs,
  orbit-symmetric S, wreath/direct products of non-abelian groups, nilpotent groups, plain graph annealing, bi-Cayley
  graphs with semi-edges or loops, non-bipartite cubic bases with a parity.
