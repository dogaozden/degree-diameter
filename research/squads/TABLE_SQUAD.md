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
| (6,8) | 30,576 / 29,790 | **31,200** | SL(2,25), S = 3 orbits of size 2 under conjugation (ORBIT="2 3 0"), found by Opus solo | build_haar2.py VALID; apsp.c all-pairs diameter 8 (table_squad/checks/d6D8_sl_25_1_orb2f0_s1.check.txt) |

(6,8) had resisted the orbit search with k = 3: with Δ = 6 that leaves only two orbits, and STRUCTURE.md §8 found no
symmetric solution at all at N ≈ 15,500. With k = 2 there are three orbits (a much larger space), and at D = 8 a fixed
point costs only e^(−λ/2) ≈ 0.04, so the price of the symmetry is small. SL(2,25) solved in 201 s.

## Squad rounds

(filled in as the rounds finish)
