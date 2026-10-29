# Cell (9,9): raise the orbit-symmetric Haar record (job raise-9-9, round 2)

Record to beat: **3,499,776** (= 2·N, N = |PSL(2,7) × SL(2,7) × Z_31| = 1,749,888; k = 3, m = 3, f = 0, μ = 30.5;
file research/frontier/sols/d9D9_prod_psl_7_sl_7_31_orb3f0_s1.txt). Table 2,961,536; Moore bound 38,347,922.

Round 1 (branch claude/raise-d9d9-record-4vxjz9, notes in its cells/raise-d9D9.md): 16 annealing runs of 3,000–3,600 s on
sl 29 73, sl 121 1, prod sl 9 psl 17 1, prod sl 4 sl 31 1, prod psl 3 sl 13 67 (k = 3, f = 0). Best costs 6–20, none
reached 0. Round 1 ended with: "not raised", and listed as untried: more core-hours at μ 31–33, metacyclic lifts, f = 3,
SL(3,q) centralizers.

## Round 2: what was tried (this branch)

Code: research/structured/haar_sym.c gained a `GENS` mode (env `GENS="c:r,..."`, `GENSCAN=1` or `GENSAMPLE=m`,
`FINDCONJ=o`, `QINV=i`, `GENSDBG`, `LEVELS`). S is the orbit of one point under a group B of automorphisms
x ↦ (c x c⁻¹, r z), accepted when |Bx| = d. Solutions (cost 0) are written with the full diameter check.
The point of the mode: a single orbit of size 9 has ~N/9 candidates, so one can scan all of them (≈ 8 min per group
at 2.6 ms per evaluation) instead of annealing. If the Poisson model held (ε ≈ 2, see SIZE_LAW §2.2) a group with
μ ≈ 30 would have ~10² solutions among those N/9 orbits.

Results (D = 9, d = 9 unless noted; costs are uncovered elements):

| group | N | B | random-S min (samples) | orbit min | reading |
|---|---|---|---|---|---|
| sl 17 × Z_361 (9-scaling) | 1,767,456 | Z9 = ⟨(c_g9, r9)⟩ | RANDSAMPLE 328–338 | 446 (2,000) | cyclic Z_361 mixes badly |
| psl 19 × Z_523 (9-scaling) | 1,788,660 | Z9 | 417 (2) | 562 (2,000) | same |
| psl 19 × Z_79 at D = 8 (9-scaling, r of order 3) | 270,180 | Z9 | 26 (200) | 122,694 | σ³ fixes all of Z_79: ball growth collapses |
| prod psl 7 sl 7 × Z_31 (record group) | 1,749,888 | Z3² = ⟨(c_x, 5), (c_y, 1)⟩ | 42 (K = 3 family) | 2·10⁶–3·10⁶ | orbits generate small subgroups (|⟨S⟩| = 10⁴–2.5·10⁵) |
| meta 583296 ⋊ Z_3 | 1,749,888 | — | RANDSAMPLE 9.9·10⁵ | — | abelian index-3 subgroup: dead |

Reading. A cyclic order-9 automorphism needs every prime of n to be ≡ 1 mod 9 (so that σ³ has few fixed points), and
that rules out every group in the window with a large nonabelian factor. A Z3² acting on a Z_p factor always has an
element trivial on Z_p, with fixed set |C_Q| · p, and on the record group those orbits mostly fail to generate G.
So the K = 9 idea does not work with the groups available at this order.

Triple and pair products in the window (enumerated; solvable factors SL(2,3)/PSL(2,3) dropped as poor mixers):
prod psl 5 psl 5 × Z_487 (N 1,753,200, μ 31.2, |Fix| 8): random K = 3 orbits min 225, median 2,373. Dead: the cyclic
factor 487 is too large for a 3,600-element nonabelian part. The other window groups with small |Fix| are either already
in round 1's screen or have a cyclic factor of similar size.

## K = 3 rungs (this round; K 8, THREADS 1; haar_sym's reported cost; logs in research/structured/runs/raise-d9D9-r2/)

Phase A, 1 h each (seed 21–24):

| group | N | μ | |Fix| | best cost | evals |
|---|---|---|---|---|---|
| prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 161 | 12 | 1.0·10⁶ |
| sl 121 1 | 1,771,440 | 35.3 | 119 | 10 | 7.0·10⁵ |
| prod psl 3 psl 19 43 | 1,764,720 | 33.7 | 26 | 15 | 7.8·10⁵ |
| prod psl 3 sl 13 67 | 1,755,936 | 31.8 | 35 | 20 | 7.6·10⁵ |

Phase B, 2.5 h each (seeds 25–29; RESTART=1 and plain variants; one ORBW=3 run was stopped at cost 20 after 29 min):

| group | N | μ | seed, variant | best cost | evals |
|---|---|---|---|---|---|
| prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 27, RESTART=1 | **5** | 2.5·10⁶ |
| prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 29, RESTART=1 | 8 | 2.0·10⁶ |
| sl 121 1 | 1,771,440 | 35.3 | 26, plain | 8 | 1.7·10⁶ |
| sl 121 1 | 1,771,440 | 35.3 | 25, RESTART=1 | 6 | 1.8·10⁶ |

None reached cost 0. The best run is prod sl 9 psl 17 1 seed 27: cost 5 after 2.5·10⁶ evaluations, stuck at 5 from about
10 min onward. Nothing was written to research/frontier/sols/, so there is nothing to verify.

## Verdict (round 2, about 4 h of compute on 4 cores)

**Not raised.** The record stays at 3,499,776.

- The K = 3 family reaches a wall at μ ≈ 31–35 for every group in the window. Round 1 and round 2 together: 24 runs, the best
  cost 5 (prod sl 9 psl 17 1). Only the record group (|Fix| 17) has been solved.
- K = 9 single-orbit scans (new mode, GENS) failed for the structural reasons in the table above. Cyclic Z_9 needs
  primes ≡ 1 mod 9 in n, which leaves only SL(2,17)×Z_361 and PSL(2,19)×Z_523 in the window, both with poor mixing.
- Metacyclic groups and triple products with solvable factors are dead; the surviving triple product A5×A5×Z_487 has
  random min 225.

Not tried, for the coordinator: the cheaper orbit evaluation of STRUCTURE §7.4 (about +2 in μ); SL(3,q) centralizers
(STRUCTURE §7.3); k = 3 with f = 3, m = 2. Any of these needs an implementation first. Next cheapest test: several seeds of
prod sl 9 psl 17 1 with RESTART=1 for another 10 core-hours; its trajectory is the only one that went below 8.


Record to beat: **3,499,776** (= 2·N, N = 1,749,888 = |PSL(2,7) × SL(2,7) × Z_31|). Table 2,961,536; Moore bound 38,347,922.
Rounds 1 and 2 (branches claude/raise-d9d9-record-4vxjz9 and claude/raise-d9d9-record-r2-iuebf3) did not raise it. Their
notes are in cells/raise-d9D9.md on those branches. Round 2's best lead was prod sl 9 psl 17 1 (cost 5, μ 33.2, |Fix| 161).

## Round 3: setup and what changed

- haar_sym.c is the round-2 version (GENS mode included); no code changes this round.
- Orbit screen over the whole window N ∈ [1,749,889, 1,766,000] with the cyclic-factor rule relaxed (`orb_screen.py --anyn`,
  RANDORB 300 samples each, 1 thread). Round 1 and 2 used only n with all primes ≡ 1 mod 3, which excludes the
  lowest-μ group in the window.
- Calibration on the record group (prod psl 7 sl 7 x Z_31, solved in round 1 after 1.26·10⁶ evaluations, μ 30.50, |Fix| 17):
  RANDORB min 42, p1 51, p10 96, median 203.
- New lead: **psl 73 × Z_9** (N = 1,750,248, μ 30.58, |Fix| 107, fixed-point misses ~5.6), never tried before. RANDORB
  min 53, p1 60, p10 93, median 157, i.e. the same lower tail as the record group and a μ just above it.
  Compare prod sl 9 psl 17 1 (μ 33.2, misses ~8.6, stalled at cost 5). The α is conj by an order-3 element times z → 4z on Z_9.

## Runs (THREADS 1, nice 10, timeout 9600 s, K 3, d 9, D 9, f 0)

Logs in research/structured/runs/raise-d9D9-r3/. Solutions (if any) would go to research/frontier/sols/ with the d9D9_ prefix.

| group | N | μ | |Fix| | seed | variant | status |
|---|---|---|---|---|---|---|
| psl 73 x Z_9 | 1,750,248 | 30.6 | 107 | 51 | RESTART=1 | 9,000 s, **best 15**, 4.22·10⁶ evals, no solution |
| prod psl 3 sl 13 67 | 1,755,936 | 31.8 | 35 | 41 | RESTART=1 | 9,000 s, **best 14**, 2.59·10⁶ evals, no solution |
| prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 161 | 43 | RESTART=1 | 9,000 s, **best 4**, 2.99·10⁶ evals, no solution |

Round 3 results so far: best cost 4 (prod sl 9 psl 17 1, the lowest cost of rounds 2 and 3 on that group, down from 5 in
round 2), 14 (prod psl 3 sl 13 67, down from 20 in round 2's 1 h run), 15 for psl 73 × Z_9 at 7,300 s.
No run reached cost 0, so nothing was written to research/frontier/sols/.

Follow-up launched at about 04:10 UTC on the two free cores: prod sl 9 psl 17 1, seeds 61 and 62, RESTART=1, 9,000 s each.
Their logs are in runs/raise-d9D9-r3/.

### Round 3: anyn screen result (window 1,749,889–1,766,000; RANDORB 300 samples each)

Full table: runs/raise-d9D9-r3/screen_anyn_window.txt (the ranked part is the second half; the first 60 lines are the unsorted
list). Top of the ranking by (p1+p10)/2 (fix = |Fix(α)|):

| rank | group | N | μ | fix | min | p1 | p10 | median |
|---|---|---|---|---|---|---|---|---|
| 1 | prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 161 | 54 | 57 | 94 | 210 |
| 2 | psl 73 x Z_9 | 1,750,248 | 30.6 | 107 | 53 | 60 | 93 | 157 |
| 3 | prod psl 9 sl 17 1 (PSL(2,9) x SL(2,17); a different group of the same order to rank 1) | 1,762,560 | 33.2 | 161 | 46 | 63 | 94 | 215 |
| 4 | prod psl 3 psl 19 43 | 1,764,720 | 33.7 | 26 | 45 | 79 | 121 | 258 |
| 5 | prod sl 3 psl 13 67 (= prod psl 3 sl 13 67) | 1,755,936 | 31.8 | 35 | 78 | 99 | 148 | 378 |

Calibration: the record group (prod psl 7 sl 7 x Z_31, solved) gives min 42, p1 51, p10 96, median 203 on the same sampler.
So psl 73 x Z_9 has the record group's lower tail at μ 30.6 (the lowest μ above the record); rank 1 and 4 are the other leads.
Caveat: 300 samples per group; the lower tail of a random sample predicts the start point, not the search outcome.

## Round 3 verdict (about 5 h of compute on 3–4 cores)

**Not raised.** The record stays at 3,499,776. No run reached cost 0, so nothing was written to research/frontier/sols/.

Final results (all K = 3, m = 3, f = 0, RESTART=1, 9,000 s each, THREADS 1):

| group | N | μ | |Fix| | seed(s) | best cost | evals |
|---|---|---|---|---|---|---|
| prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 161 | 43 | **4** | 2.99·10⁶ |
| prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 161 | 61 | **4** | 2.89·10⁶ |
| prod sl 9 psl 17 1 | 1,762,560 | 33.2 | 161 | 62 | 8 | 2.92·10⁶ |
| psl 73 x Z_9 | 1,750,248 | 30.6 | 107 | 51 | 15 | 4.22·10⁶ |
| prod psl 3 sl 13 67 | 1,755,936 | 31.8 | 35 | 41 | 14 | 2.59·10⁶ |

Reading. Across rounds 2 and 3 the sl 9 psl 17 1 group reached cost 4 in three independent seeds and never 0. Round 1 and 2 had
cost 5 there. So the group has a clear floor at 4 uncovered elements under this annealer. Its fixed-point misses
(~8.6 by the §1 model) are the likely cause; the cost-4 states are probably a few fixed elements uncovered.

Lessons for the coordinator:
- The screen (orb_screen.py --anyn, window 1,749,889–1,766,000) found no group with a better random-orbit tail than
  these. psl 73 × Z_9 (μ 30.6) matched the record group's tail but stalled at cost 15.
- prod psl 3 psl 19 43 (|Fix| 26, rank 4 in the screen) got only the round-2 one-hour run. It is the one untested
  low-|Fix| lead in the window.
- A dedicated fixed-point fix (ORBW=k weighting, or a cheaper orbit evaluation from STRUCTURE §7.4 for q ≥ 64; sl 121 1
  qualifies) is the next thing that could move the cost-4 floor. Neither was tried here.

Not done this round: SL(3,q) centralizers (STRUCTURE §7.3), the §7.4 evaluation, k = 3 with f = 3 at m = 2 (§8 already
found f = 0 better at (9,8)).
