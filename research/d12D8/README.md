# Cell (12,8): tools and notes (cell-12-8 job, 2026-10-24)

Goal: a bipartite graph of maximum degree 12 and diameter 8 on more than 4,650,100 vertices (DS14v2 table value,
unchanged since 2013; bipartite Moore bound 42,871,776).

## What the table value is (decoded, not from the paper)

The D = 7 and D = 8 table entries for Δ ≥ 10 are exact multiples of the generalized hexagon H(q)
(n = (q^6−1)/(q−1) points = lines):

| cell | table | = | q | Δ − (q+1) |
|---|---|---|---|---|
| (12,7) | 664,300 | 2·5·|H(9)| | 9 | 2 |
| (12,8) | 4,650,100 | 2·35·|H(9)| = 7·(12,7) | 9 | 2 |
| (10,8) | 1,176,480 | 2·30·|H(7)| | 7 | 2 |
| (11,8) | 2,246,940 | 2·30·|H(8)| | 8 | 2 |
| (14,8) | 14,172,480 | 2·40·|H(11)| = 8·(14,7) | 11 | 2 |
| (16,8) | 36,201,060 | 2·45·|H(13)| = 9·(16,7) | 13 | 2 |
| (13,8) | 5,314,680 | 2·15·|H(11)| = 5·(13,7) | 11 | 1 |

D = 7 with Δ = q+1+k is Delorme's X(M): 2k+1 copies (levels) of H(q), hexagon edges inside a level, k hop
matchings point → line between levels i and i+j (research/squads/exp2/hexd7/README.md proves diameter 7 for any
bijections M). At D = 8 with k = 2 the multiplier is 5·(⌊Δ/2⌋+1), i.e. the (Δ,8) graph has (⌊Δ/2⌋+1) times the
vertices of the (Δ,7) graph X_2(M). Working hypothesis: Delorme's (12,8) graph is a Z_7-lift of X_2(M) at q = 9
(lift of "hexagon + 2 hop matchings" by a group of order 35). The paper (Delorme, J. Graph Theory 9 (1985)) could not
be read (paywalled; the CombinatoricsWiki page fails TLS from the container).

## Tools (tools/)

- `hexgen.c`: H(q) for q = p, p² (odd p), copied from research/p4/d6. `./hexgen q` writes hex/hex_q{q}.bin
  (hex/ is not committed; regenerate). Built here for q = 3, 5, 7, 9.
- `hexlib.py`: load H(q), write base files.
- `liftcheck.c`: **the scorer.** Base multigraph (points | lines, edges with voltages in a group of order ≤ 64, cyclic or
  given by a table) → for every point source (or every STEP-th), BFS in the lift to depth 7 and count uncovered
  (line, group element) pairs. 0 uncovered from all sources ⇔ the lift has diameter ≤ 8 (opposite pairs ≤ 7). Usage
  `liftcheck BASE [MAXLEN=7] [STEP=1]`. At q = 9 a full check (66,430 sources) takes ~3 min on 4 threads; STEP=331
  (201 sources) ~1 s. Build `gcc -O3 -march=native -fopenmp -o liftcheck liftcheck.c`.
- `nbwalks.c`: number of non-backtracking walks of length ≤ 7 from one point to every (line, level) target.
- `mk_xm.py`, `mk_rand.py`, `mk_var.py`: generators for Delorme X(M) lifts and variants.
- `lsearch.c`: annealing over all voltages (hexagon + k random hops, Z_N) with exact evaluation (small q only).

## Measurements so far (q = 9 unless noted)

- Random voltages on hexagon + 2 random hops: 0 sampled misses at N = 12, 1 at N = 16, 37 at N = 20 (201 sources).
  Delorme reaches N = 35. So the table graph is far beyond random-like lifts (as SIZE_LAW said: above the
  first-moment ceiling).
- Constant hop voltages (pure level structure, hexagon voltage 0): only ~3k+1 = 7 levels are guaranteed for
  arbitrary M (q = 3: N = 9 ok, 10 nearly).
- Walk counts (length ≤ 7, per (line, Z_5-level) target) in X_2 with random M: mean 64.5, minimum 6–11 over
  sources; the minima are near lines (hexagon distance 1, 3) at level difference 0. Structured M raise the minimum:
  M2 = M1: 15; two perfect matchings of the incidence graph ("inc"): 20–26; one incidence matching used for both
  hops (triple edges, "incsame"): 25–27.
- Random second factor Z_7 on any of these bases: ~900–1300 misses per source. The voltage design is the crux.
- q = 3 (Δ = 6): annealing reaches N = 28 (Delorme's formula gives 20); random-like methods are strong at small q,
  so small q says little about q = 9.
