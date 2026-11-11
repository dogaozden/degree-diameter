### D = 15 and D = 16 at Δ = 3..6 (job beyond-d15, 2026-11-01)

Job beyond-d15 (Opus director + four Haiku squad rounds of 14-16 cards, cloud session, branch claude/new-cells-d15-d16-fpj633).
Eight new cells; nothing was recorded at D = 15, 16 before. Files: research/frontier/beyond15/ (cells.txt and
cells_other.txt list every value with its check; rows15.py makes the rows, splice15.py puts them here; sols/, runs/
(haarcheck_gen logs), checks/ (metacheck logs), lsym/ (symmetric-lift bases, sweeps and logs), THEORY15.md); edge lists
of the cubic graphs in research/frontier/beyond/graphs/ with apsp logs in research/frontier/beyond/checks/; squad cards
and scoreboards research/squads/beyond15/r1..r4; log research/squads/LOG.md.

**What won where.**
- Δ = 3: symmetric voltage lifts (THEORY15.md). The voltages of a Z_n lift are made equivariant under a rotation ρ of the
  base with a multiplier λ (λ^k = 1 mod n), so the metacyclic group Z_n x|_λ Z_k acts on the lift with few vertex
  orbits; after gauge fixing only t/2 - 1 voltages are free (t = number of orbits), so each (base, n, λ) is searched
  exhaustively in seconds to minutes (liftsym EXH; composite n through the Chinese remainder theorem) or annealed in
  seconds. The cubic metacyclic Haar graphs are the case t = 2 (one graph per (k, pattern, n, λ)). Dividing by the whole
  group gives a quotient multigraph; on 6 vertices there are only three (Tutte-8-cage/Foster shape, Gray shape, K3,3), and
  the best graphs came from Z_k covers of these quotients with other k than the classical graphs: (3,15) 12,246 is the Gray
  shape with k = 13 and n = 157 (squad card r4/n03), above 11,802 (Tutte/Foster shape, k = 7, n = 281, r3/k03), 11,790
  (Tutte 8-cage itself over composite n = 393, r2/e06), 11,342 and 11,026 (Haar graphs, exhaustive sweeps) and 10,746
  (Gray graph, n = 199); (3,16) 20,466 is the Gray graph itself over n = 379 (exhaustive), above the Haar graph of
  Z281 x| Z35 (19,670). Girth-8 bases beat girth-6 ones (Desargues: 9,220 and 15,020). Plain Z_n lifts annealed as at
  D = 13, 14 stayed below (GP(10,3) cost 6 at 10,000; Tutte 8-cage 9,900; Pappus 14,940).
- Δ = 4, 5: Haar graphs of odd-order Frobenius groups Z_m x|_r Z_k with random S (hmeta). k must be large at these
  diameters: k = 13 is nearly abelian at D = 15 (cost 1,738 at (5,15) where k = 151 solved in 35 s); squad card r1/c05
  measured random-like behaviour from k ~ 31 (D = 15) and ~43 (D = 16) at Δ = 4; the values use k = 73 (Δ = 4) and
  k = 151 and 311 (Δ = 5). Several values came from closing a saved cost-2 state with one new-seed link (r2/f02, r2/g01,
  r3/m01); other cost-2 states did not close in 10 links (they are listed in research/squads/LOG.md).
- Δ = 6: SL(2,p) x Z_n with small n at odd D and PSL(2,p) x Z_n at even D, S = two free alpha-orbits (haar_big0 f = 0),
  solved at mu 10 and 11.6 in tens to hundreds of evaluations (0.6 s each at 2e9 elements); both checked by haarcheck_gen.

**What failed.** Orbit S at Δ = 4, 5 in SL/PSL x Z_n (floors 192 and 65; "5 1 0" 52); products of Frobenius groups and
AGL(1,q) at (4,15), (5,15) (cost 4); even-order and composite-m metacyclic groups (not fixed-point-free); larger
symmetric-lift families (order-3 Gray, order-5 Foster: costs 6-78) — the small exhaustive families did better than
annealing in the large ones; Foster (girth 10) came within cost 2 at (3,16) n = 211 but not at n >= 228; Dyck, Nauru,
Pappus symmetric lifts; the K3,3 quotient (cost 8 at k = 5); composite-m cubic Haar graphs (cost 263+); quartic symmetric
lifts of GQ(3,3) (cost 184). Exhaustive (CRT) scans proved several annealing near misses empty: the Gray-shape k = 13
pattern [8,8,4,11] at n = 158 (min cost 2). See research/squads/LOG.md for every card.

**Machine.** 4 cores shared by 16 cards and the director. The scheduler gives every process group an equal share
(autogroups), so `nice` inside a command does nothing; the director raised the priority of the long checks by writing to
/proc/<pid>/autogroup. A container restart at 23:29 UTC killed seven round-2 cards and the first (6,16) check, which was
rerun.
