# exp2-alone-1: report

Job: one Haiku worker, alone, on the three D = 7 cells of the bipartite (Δ, D) table. Focus cell (7,7). Start
2026-10-24 16:56 UTC; final check 17:56 UTC (wall time about 1 h). Budget at the last check: 0.005 units (cap 1.5).
Branch: `claude/exp2-alone-1-d7-cells-91ki6i`.

## Result

**No cell beaten.** Best valid graph per cell, each checked VALID by `research/frontier/build_haar2.py` (diameter 7,
every vertex reached, regular degree Δ, no repeated edges):

| cell | table (vertices) | our best (vertices) | ratio to table | group | file in `research/frontier/sols/` |
|---|---|---|---|---|---|
| (7,7) | 23,436 | **19,152** | 0.817 | SL(2,8) × Z₁₉ (N = 9,576), orbit k=3, m=2, f=1 | `d7D7_sl8p19_Z19_orb3_s3.txt` |
| (9,7) | 117,648 | **82,992** | 0.705 | SL(2,13) × Z₁₉ (N = 41,496), orbit k=3, m=3, f=0 | `d9D7_sl13_19_orb3f0_s1.txt` |
| (11,7) | 398,580 | **266,448** | 0.669 | SL(2,13) × Z₆₁ (N = 133,224), orbit k=3, m=3, f=2 | `d11D7_sl13_61_orb3f2_s13.txt` |

Vertices = 2N (each side has N = |G| vertices). Ratios are best valid size divided by the table value. Other valid
(7,7) and (11,7) graphs found on the way are also in `sols/`: (7,7) SL(2,11)×Z₇ (18,480) and SL(2,9)×Z₁₃ (18,720);
(11,7) SL(2,16)×Z₃₁ (252,960).

## What I did

1. Read `research/frontier/PLAN.md`, `SIZE_LAW.md`, and the orbit-mode notes (`research/structured/STRUCTURE.md`,
   on branch `claude/structured-search-orbit-w5dd4f`, which I fetched). I built `haar_sym` from that branch in my
   scratchpad. Nothing from that branch was merged into this branch.
2. Used the orbit recipe from the notes: G = SL(2,q) × Z_n with every prime factor of n ≡ 1 (mod 3); S is closed
   under an automorphism α of order 3 (conjugation by an order-3 element, times z ↦ rz on Z_n). `ORBIT="k m f"` is
   set to `"3 m f"` with d = f + 3m. Δ ≡ 1 (mod 3) uses f = 1, Δ ≡ 2 uses f = 2, Δ ≡ 0 uses f = 0 (free orbits only).
3. Checked each group's Poisson mean μ = N·e^(−W/N), with W = 1 + Σ Δ(Δ−1)^(2i−1) (i = 1..3) for D = 7, against the
   wall. Orbit runs solved up to about μ ≈ 32–33 in minutes and failed at μ ≈ 35–48 (below). Each group was run with
   `haar_sym`'s own full diameter check, then independently re-checked with `build_haar2.py` before saving.

## Runs (solved in bold)

(7,7), target 23,436 (needs N ≥ 11,718; the wall is about N ≈ 10k):

| group | N | μ | outcome |
|---|---|---|---|
| SL(2,11) × Z₇ | 9,240 | 21.6 | **solved in 20 s** (18,480) |
| SL(2,9) × Z₁₃ | 9,360 | 23.6 | **solved in 20 s** (18,720) |
| SL(2,8) × Z₁₉ | 9,576 | 27.7 | **solved in 20 s** (19,152, best (7,7) result) |
| SL(2,4) × Z₁₆₃ | 9,780 | 31.9 | failed, best 36 after 575 s |
| SL(2,4) × Z₁₆₉ | 10,140 | 40.6 | failed, best 42 after 900 s |
| SL(2,7) × Z₃₁ | 10,416 | 48.2 | failed, best 6 after 1,500 s (two seeds: 6 and 6) |
| SL(2,3) × Z₄₀₉ | 9,816 | 32.7 | failed, best 1,460 (solvable small Q: no good) |
| SL(2,3) × Z₄₂₁ | 10,104 | 39.6 | failed, best 1,832 |
| SL(2,4) × Z₁₈₁ | 10,860 | 62.6 | killed early, best 96 |
| SL(2,5) × Z₉₁ | 10,920 | 64.8 | killed early, best 50 |

(9,7), target 117,648 (needs N ≥ 58,824; the wall is about N ≈ 41–44k):

| group | N | μ | outcome |
|---|---|---|---|
| SL(2,13) × Z₁₉ | 41,496 | 30.4 | **solved in < 60 s** (82,992, best (9,7) result) |
| SL(2,5) × Z₃₄₉ | 41,880 | 32.8 | failed, best 48 after 900 s |
| SL(2,7) × Z₁₂₇ | 42,672 | 38.1 | failed, best 12 (stopped at 616 s) |
| SL(2,9) × Z₆₁ | 43,920 | 47.9 | failed, best 16 (stopped at 616 s) |
| SL(2,5) × Z₃₆₁ | 43,320 | 43.0 | failed, best 104 after 900 s |

(11,7), target 398,580 (needs N ≥ 199,290; the wall is about N ≈ 133–137k):

| group | N | μ | outcome |
|---|---|---|---|
| SL(2,16) × Z₃₁ | 126,480 | 19.4 | **solved in < 60 s** (252,960) |
| SL(2,13) × Z₆₁ | 133,224 | 31.8 | **solved in 18 s** (266,448, best (11,7) result) |
| SL(2,7) × Z₃₉₇ | 133,392 | 32.2 | failed, best 60 after 900 s |
| SL(2,11) × Z₁₀₃ | 135,960 | 38.4 | failed, best 6 after 900 s |
| SL(2,7) × Z₄₀₃ | 135,408 | 37.0 | failed, best 84 after 900 s |
| SL(2,8) × Z₂₇₁ | 136,584 | 40.0 | failed, best 35 after 900 s |

## What worked, what didn't

- **Worked:** orbit-symmetric S with q ≥ 8 (or SL(2,11), SL(2,13), SL(2,16)) and n ≈ 1 mod 3 primes, at μ ≤ ~32.
  Each of these solved in seconds to a minute, and the verifier confirmed them.
- **Did not work:** SL(2,3) and SL(2,4), which are solvable or small (best costs in the hundreds or the 30s–90s).
  Cyclic factors with a big prime (e.g. Z₃₉₇, Z₄₀₃) and SL(2,7) at μ ≈ 35–48. At μ ≈ 40+ the orbit search ran for
  900–1,500 s without reaching zero, which matches the wall reported in the orbit notes (μ ≈ 45–50 with ~10⁷ evals,
  less here because the groups are larger).
- **Why nothing beat a table value:** for (7,7) the table is 23,436, which needs N ≥ 11,718, i.e. μ ≈ 98 at this
  group size. The orbit wall is near μ ≈ 45–50, so the gap is far beyond what this machinery can reach in the time
  here. My rough estimate of the first-moment ceiling (Δ−1 generators per side, same Poisson model as SIZE_LAW) is
  about N ≈ 10.7k, i.e. 21.4k vertices, so the (7,7) table value looks to be above what these families can reach.
  The (9,7) and (11,7) cells are further away (ratios 0.71 and 0.67). I have not checked these estimates against
  anything beyond my own arithmetic.

## Verification

Every saved graph was checked by `research/frontier/build_haar2.py` (independent rebuild, two BFS, degree and
duplicate checks). Results: (7,7) 19,152 VALID; (9,7) 82,992 VALID; (11,7) 266,448 VALID (edge-list sha256
`87c12473f5b3…`, see the saved solution file). No low-memory checker was needed (all below 300k vertices).

## Budget and time

- Wall time: 16:56 to 18:06 UTC, when the last search ended (1 h 10 min); the cap was 4 h.
- `budget_units`: about 0.005 at the last check (cap 1.5). The log is `research/squads/usage/exp2-alone-1.jsonl`.
- No subagents were used. Compute: up to 4 single-thread `haar_sym` runs at a time.

## What to try next (not done)

- (7,7): needs a construction that beats the orbit wall (μ ≈ 45–50). Random and orbit S both top out around 20k
  vertices here, so this is probably a new family, not more compute.
- (9,7), (11,7): try higher-order groups with two orbit sets (k=3, m=4 or 5 at Δ = 9, 11 with f=0/2). Gains of a few
  percent are plausible; a 2–3× step would need a new idea.
- Seed variance was not explored at the walls (μ ≈ 35–48). More seeds on SL(2,7)×Z₃₁ and SL(2,11)×Z₁₀₃ might
  matter there, but the cost-6 floor suggests not.
