# Cell (Δ, D) = (6, 8), bipartite: raise attempt, round 3 (job "raise3-6-8", branch claude/raise3-6-8-ec4shp)

## Status
- Record held: **31,680 vertices** (2N, N = 15,840, Haar graph PSL(2,11) x Z24, ORBIT "2 3 0",
  `research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`). Table value 29,790; Moore bound 195,312.
- This round: **no improvement**. No solution found for any 2-fiber bi-Cayley lift with |G| >= 7,921 (V = 4|G| >= 31,684).

## What was built (research/squads/raise3-d6D8/)
- `mkgroup.py`: group tables of PSL(2,q) / PGL(2,q) (q = 7, 8, 9, 11, 13), order-asserted.
- `bicay.c`: simulated annealing over voltage sets of a 2-fiber lift of degree d = 6 on G = H x Z_n (n <= 64).
  Bit-parallel BFS from the four fiber roots. Cost = uncovered vertices within distance D, summed over roots.
- `verify.py`: independent Python checker (explicit graph, structure, 4-root diameter; `--full` for all-pairs BFS).
  Its costs match the C evaluator exactly on saved states (42 = 42, 36 = 36, 91,560 = 91,560, 70 = 70).
- `autos.py`: inner automorphisms of order 2 or 3 (for orbit-symmetric voltage sets).

## Results
| run | |G| | V = 4|G| | A | best cost | evals | outcome |
|---|---|---|---|---|---|---|
| control | 7,056 (psl8 x Z14) | 28,224 | 2 | 2 | 2.5M (900 s) | no solution |
| control | 7,056 (psl8 x Z14) | 28,224 | 3 | 4 | 2.5M | no solution |
| control | 7,056 (pgl7 x Z21) | 28,224 | 3 | 2 | 3.8M | no solution |
| control | 7,260 (psl11 x Z11) | 29,040 | 3 | 4 | 1.9M | no solution |
| calibration | 8,064 (psl8 x Z16) | 32,256 | 3 | 40 | 0.4M (150 s) | no solution |
| calibration | 8,064 (psl8 x Z16) | 32,256 | 2 | 32 | 0.4M | no solution |
| calibration | 8,064 (pgl7 x Z24) | 32,256 | 3 | 36 | 0.6M | no solution |
| campaign (40 min each) | 8,064 (psl7 x Z48) | 32,256 | 3 | 26 | 19.6M | no solution |
| campaign | 8,064 (psl8 x Z16) | 32,256 | 2 | 28 | 6.5M | no solution |
| campaign | 8,064 (pgl7 x Z24) | 32,256 | 3 | 28 | 9.8M | no solution |
| campaign | 8,064 (psl8 x Z16) | 32,256 | 3 | 30 | 6.6M | no solution |

Symmetric voltage sets (orbits of an inner automorphism of order 2, or z -> -z on Z_n) do much worse: plateaus of
70-74 and 91,560 (7056, A=2). Dropped.

## Why I stop here
- The annealer cannot solve lifts even at V = 28k, where it stalls at cost 2-4 after 2-3 M evaluations. The Haar
  annealer solves the record cell (V = 31,680) in about 46 s. So this lift annealer is far weaker than the Haar one, and
  a failure at 8,064 says little about the lift family.
- The plateaus at 8,064 (26-30) are reached within 5-10 minutes and barely move afterwards.
- Within the time I had, I can't tell whether the family can beat 31,680. This is an unfinished route, not a refutation.

## Next steps (for a stronger worker)
1. Improve the lift annealer: better moves (swap the two blocks' sets, or a move that changes one fiber's set
   as a whole), a tabu list, or restarts from the best plateau state. Check it reaches 0 at V = 28k in a few minutes
   before running at 8,064.
2. Use the orbit idea differently: an automorphism that swaps the two fibers on each side (rather than inner
   automorphisms of G), which keeps the variable count without the plateaus seen here.
3. Keep the independent check (verify.py --full, or apsp.c) for any solution; save it as d6D8_bicay_* in sols/.

## Haiku notes
Log: `research/squads/raise3-d6D8/NOTES.md`. Run logs: `research/squads/raise3-d6D8/runs/`.
