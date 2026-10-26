# Raise the (Δ,D) = (6,9) record: notes for resumption

Job "raise-6-9" (Haiku worker). Record to beat: **127,296 vertices** (Haar graph of SL(2,17) × Z13, N = 63,648,
orbit k=3, m=2, f=0; `research/frontier/sols/d6D9_sl_17_13_orb3f0_s2.txt`). Table 117,360; Moore 976,562.
Every new record needs N ≥ 63,649 (vertices = 2N).

## Method

- Tool: `research/structured/haar_sym` (orbit-symmetric annealing, STRUCTURE.md §1, §8). Build:
  `gcc -O3 -march=native -fopenmp haar_sym.c -o haar_sym -lm` (warnings only).
- Command shape: `ORBIT="3 2 0" haar_sym 6 9 <secs> <seed> 8 <out> <group> <n>`, THREADS=1, under nice.
- Reproduced the record: `sl 17 13`, seed 2, 34k evaluations, 2.7 s.
- Candidate orders from `tools/orb_screen.py 6 9 63649 80000 "3 2 0" --list` (μ = N e^(−W/N), W = 488,281).
  Each +1 % in N raises μ by about 9 %. Evaluations to solve grow like e^(μ/4.5) (STRUCTURE §3, §8).
- Job queue: `tools/pool.sh` with spool `<scratchpad>/spool`, `tools/orbq.sh` per job file. Solutions and
  logs go to the spool; a VALID one is copied into `research/frontier/sols/` and `research/structured/runs/`.

## Log

- (start) binary builds, record reproduces. Wave 1: μ ≈ 30–40 candidates, 600 s, seed 1.
- Wave 1 batch A (600 s, seed 1, ~9e6 evals each, all unsolved):
  sl 8 × 127 (N 64008, μ 31.1): best 46; psl 7 × 379 (N 63672, μ 29.7): best 138;
  sl 11 × 49 (N 64680, μ 34.1): best 14; sl 7 × 193 (N 64848, μ 34.8): best 96.
  Reading: group family matters more than μ. Small q (7, 8) and psl 7 are poor. The record's group
  SL(2,17) × Z13 solved at μ 29.7 in ~6e4 evals. Prefer large prime q with small prime n.
- Candidates still open, N ≥ 63,649 with every prime of n ≡ 1 mod 3 (orb_screen list): psl 19×19 (64980),
  psl 11×97 (64020), psl 13×61 (66612), sl 13×31 (67704, μ 50), psl 9×181 (65160), sl 41×1 (68880, μ 57.5),
  psl 27×7 (68796), sl 9×91 (65520).
- Wave 1 batch B (600 s, seed 1): psl 19 × 19 (N 64980, μ 35.4, |Fix| 8): **best 3** (6.4M evals);
  psl 13 × 61 (N 66612, μ 43.7): best 12; psl 11 × 97: best 18; sl 9 × 91: best 62;
  psl 9 × 181 (N 65160): best 84; sl 41 × 1 (N 68880, μ 57.5, |Fix| 41): best 24.
- Wave 2: psl 19 × 19 seeds 2, 3 at 1200 s: both stuck at 3 after 5.3M evals. ORBW=3 variant (seeds 1, 2).
  Odd D and PSL: PSL(2,q) has ~q²/4 involutions, each missed with prob about e^(−λ/2), so a floor of a few
  misses is expected (STRUCTURE §2.6, §5). SL(2,q) has only −I. That may explain the plateau at 3.
- Wave 3 (queued): sl 13 × 31 (N 67704, μ 49.9, large q so small |Fix|), seeds 1, 2 at 1200 s.
- Wave 3 results: sl 13 × 31 (N 67704, μ 49.9, |Fix| 11): seeds 1, 2 at 1200 s (14M evals each), seed 3 at 570 s: all
  **best 6**; ORBW=3 seeds 1, 2 at 570 s: best 6. sl 11 × 49 seed 2 at 1200 s: best 14 (24M evals so far).
  psl 19 × 19 with ORBW=3 at 900 s: best 3. Stopped the plain psl 19 × 19 runs at 1200 s (stuck at 3 on all seeds).
- Status at 09:10: no candidate has reached cost 0. The plateaus (3 for psl 19 × 19, 6 for sl 13 × 31, 14 for sl 11 × 49)
  are the same across seeds and ORBW weights, which points to a structural floor, not too little search.
  Queued 90-minute runs of sl 13 × 31 (seeds 3, 4; ORBW=3 seeds 1, 2) as the last attempt on this family.
- Wave 4 (final): sl 13 × 31 seeds 3, 4 at 90 min: **best 6** after 42M and 28M evals. ORBW=3 at 1235 s: best 6.
  psl 27 × 7 (N 68,796, μ 56.9, char 3, |Fix| n/a): best 18 after 6.6M evals. Stopped everything at 09:50.

## Conclusion (09:50, about 2 h of search)

**No record. The orbit method (k=3, m=2, f=0) is stuck in this cell with the groups it can reach.**
Every group of order 63,649 to 68,880 with every prime of n ≡ 1 mod 3 was tried, except the products (not tried,
they are small-factor and unlikely to help) and PGL twins (same order as SL, more involutions):

| group | N | μ | best cost | evals | note |
|---|---|---|---|---|---|
| psl 19 × 19 | 64,980 | 35.4 | **3** | 6–11M per seed, 4 seeds + 1 ORBW | floor (involutions) |
| sl 11 × 49 | 64,680 | 34.1 | 14 | 25M | |
| psl 11 × 97 | 64,020 | 31.2 | 18 | 7M | |
| psl 13 × 61 | 66,612 | 43.7 | 12 | 6M | |
| sl 13 × 31 | 67,704 | 49.9 | **6** | 14M, 14M, 42M, 28M, +2 ORBW | free-orbit wall (μ/k ≈ 16.6) |
| sl 9 × 91 | 65,520 | 38.0 | 62 | 6M | |
| psl 9 × 181 | 65,160 | 36.3 | 84 | 7M | |
| sl 41 × 1 | 68,880 | 57.5 | 24 | 3M | |
| psl 27 × 7 | 68,796 | 56.9 | 18 | 6.6M | |
| sl 8 × 127 | 64,008 | 31.1 | 46 | 9M | small q |
| sl 7 × 193 | 64,848 | 34.8 | 96 | 7M | small q |
| psl 7 × 379 | 63,672 | 29.7 | 138 | 0.7M | small q |

Why I think it is stuck and not under-searched:
- The record's own group solved at μ 29.7 in ~6e4 evals. Nothing at μ 31–36 solved in 6–40M evals, and most stalled 5–50× above
  the record's count. Group family dominates μ.
- The plateaus are the same across seeds and across the ORBW weight, so they look like floors, not bad luck.
- psl 19 × 19: PSL(2,19) has about 90 involutions, each missed with probability about e^(−λ/2) ≈ 0.02 (λ = W/N ≈ 7.7).
  That gives about 2 expected misses, which fits the floor of 3. The SL(2,q) groups have only −I.
- sl 13 × 31: μ/k ≈ 16.6 free-orbit misses at the start. The search reaches 2 uncovered orbits and stops. This is the
  μ ≈ 45–50 wall in STRUCTURE §6 for this budget.

What would move it (not tried; each needs more than these tools):
1. A group of order 63,649–70,000 with fewer involutions and a small centralizer of an order-3 element (SL(3,q)-type or
   SL(2,q) × SL(2,r) products), so k = 3 is usable at μ ≈ 35–40. STRUCTURE §7.3 and §8 point the same way.
2. A voltage (metacyclic or route-chart) lift of a Moore or small-cell base graph (research/lifts/, research/theorems/BEAT_16_5_SQUAD.md).
   That is a different program. Ask the coordinator whether an Opus session should take it.
3. A diagnostic: dump the uncovered set of the 6-cost sl 13 × 31 state. If it is always the same element set (for example the
   central −I or the α-fixed elements of one torus), a structural fix may exist.

Compute used: about 2 h wall clock, 4 slots, roughly 3·10⁸ evaluations in total. All solution-free: nothing was saved to
research/frontier/sols/, and the (6,9) record stays at 127,296.

## Round 2 (job raise2-6-9): exhaustive orbit pairs

Record to beat: **127,296** (N = 63,648). A new record needs N ≥ 63,649 (any N above it, e.g. 63,649 or 64,680).
Round 1 ended with no candidate solved; it sampled and annealed. Round 2 asks a different question: for one group and
one α, is there ANY orbit-symmetric S (ORBIT="3 2 0", f = 0)? That is decided by enumerating all pairs of α-orbits.

### Tools

- `research/structured/haar_sym.c`, new mode `EXHAUST="part nparts bound prefix"` (with `ORBIT="3 2 0"`): lists every
  α-orbit of size 3 once (21,000–23,000 orbits for N ≈ 64k), then evaluates every unordered pair with the same
  bitset cost as the annealer, aborting at cost ≥ bound. Zero-cost pairs are written through `check_and_write`
  (full diameter check, then s₀ = e normalisation). Pairs are split across processes by pair index.
- Speed: about 44 µs per pair at N ≈ 64k on this box. A full pass is 2.2–2.6 · 10⁸ pairs, about 45 min wall
  on 4 cores per group.
- Check on the record group (sl 17 × 13): part 0 of 2000 (112k pairs, 5 s) found 4 zero-cost pairs, all passing the
  full check. So the mode works and P(cost 0) ≈ 3·10⁻⁵ there, consistent with the record having been found.

### Cost tails (RANDORB, 200k random orbit pairs each; bins are cost/3 as in the tool)

| group | N | μ | min | cost ≤ 2 | cost 3–5 | cost 6–8 | cost ≤ 14 (bins 0–4) | note |
|---|---|---|---|---|---|---|---|---|
| sl 17 × 13 (record) | 63,648 | 29.7 | 0 | 8 | 4 | 106 | 355 | reference |
| sl 11 × 49 | 64,680 | 34.1 | 14 | 0 | 0 | 0 | 5 | |
| sl 13 × 31 | 67,704 | 49.9 | 6 (100k: 6) | 0 | 0 | 5 (per 100k) | 5 (per 100k) | |
| psl 19 × 19 | 64,980 | 35.4 | 3 | 0 | 7 | 19 | | involution floor |
| psl 11 × 97 | 64,020 | 31.2 | 18 | 0 | 0 | 0 | 0 | |
| sl 8 × 127 | 64,008 | 31.1 | 46 | 0 | 0 | 0 | 0 | |
| psl 13 × 61 | 66,612 | 43.7 | 12 | 0 | 0 | 0 | 2 | |
| sl 7 × 193 | 64,848 | 34.8 | 96 | | | | 0 | |
| sl 9 × 91 | 65,520 | 38.0 | 62 (100k) | | | | 0 | |

Reading: the record's group is about 70× richer in low-cost pairs than sl 11 × 49 at cost ≤ 14. The Poisson
model (SIZE_LAW) predicts the two to be comparable, so the group, not μ, sets the tail. This is the same finding as round 1.

### Exhaustive runs (this round)

- sl 11 × 49 (N 64,680, α = conj(mat(7,8,8,3)) × (z ↦ 18 z)): 21,556 orbits, 2.32·10⁸ pairs, 4 parts.
  **Result: no solution.** All 2.32·10⁸ pairs were checked (4 parts, 58,079,948 each, about 31 min per part).
  The minimum cost over the whole orbit-pair space is **14**, reached by about 4,000 pairs; no pair has cost
  0–13. So for this group and α there is NO orbit-symmetric S (k = 3, m = 2, f = 0) at all. Round 1's annealing
  plateau at 14 was the true optimum, not a search failure. sl 11 × 49 is closed.
- sl 13 × 31 (N 67,704, μ 49.9, α = conj(mat(3,8,0,9)) × (z ↦ 5 z)): 22,564 orbits, 2.55·10⁸ pairs, 4 parts
  (about 40 min each). **Result: no solution.** All pairs checked (63,638,942 per part); the minimum cost is **6**
  (about 2,900 pairs), nothing at 0–5. Annealing's plateau at 6 was again the true optimum for this group and α.
  sl 13 × 31 is closed. With a +6.4 % step at stake this was the most valuable cell in this round, and it is closed.
- psl 19 × 19 (N 64,980, μ 35.4, α = conj(mat(1,3,6,0)) × (z ↦ 7 z)): exhaustive pass started on the same four parts
  (`EXHAUST="p 4 15 …"`, 2.34·10⁸ pairs). Annealing floored at 3 on every seed, and the random tail showed cost 3–5 but
  nothing at 0–2. This group has 171 involutions, so the odd-D involution misses are the likely floor.
  **Result: no solution.** All 2.35·10⁸ pairs checked (58,625,499 per part). Minimum cost **3** (about 1,900 pairs),
  nothing at 0–2. The involution floor is real for this group. psl 19 × 19 is closed.
- psl 13 × 61 (N 66,612, μ 43.7, α = conj(mat(3,1,6,11)) × (z ↦ 13 z)): exhaustive pass started, 2.5·10⁸ pairs,
  4 parts. Annealing min 12 and sampled cost ≤ 14 mass about 10⁻⁵, so this is the last family with a plausible tail
  in the window. **Result: no solution.** All 2.47·10⁸ pairs checked (61,613,326 per part). Minimum cost **12**
  (about 2,900 pairs), nothing at 0–11. psl 13 × 61 is closed.

### Conclusion of round 2 (stopping here)

**No record. The orbit-symmetric method (ORBIT="3 2 0", f = 0) cannot raise (6,9) with the groups in reach.**
Exhaustive enumeration was done for every group of order 63,649 to 67,704 that has a usable tail (all of them except the
ones in the last rows of the tail table):

| group | N | μ | pairs | minimum cost | verdict |
|---|---|---|---|---|---|
| sl 11 × 49 | 64,680 | 34.1 | 2.32·10⁸ | 14 | no solution |
| psl 19 × 19 | 64,980 | 35.4 | 2.35·10⁸ | 3 | no solution (involutions) |
| psl 13 × 61 | 66,612 | 43.7 | 2.47·10⁸ | 12 | no solution |
| sl 13 × 31 | 67,704 | 49.9 | 2.55·10⁸ | 6 | no solution |

Not exhausted, and not expected to move: psl 11 × 97 (sampled min 18 in 200k), sl 8 × 127 (46), sl 9 × 91 (62),
psl 9 × 181 (84), sl 7 × 193 (96), psl 7 × 379 (138). Their sampled minima are far above zero, and the exhausted groups
reached their annealing plateaus exactly, so those plateaus are the optima too.

Why this is the end of the road for these methods:
- Within 63,649–67,704 every SL-type group with a large prime q and a small prime n ≡ 1 (mod 3) is now closed:
  the only others are the small-q or involution-heavy groups above. Any N ≥ 63,649 record must come from a group
  outside this list.
- The groups above 68,000 (sl 41 × 1, μ 57.5; others) have μ/3 ≥ 19 and expected exhaustive counts far below 1.
- PΓL(2,8) × Z_43 (N 65,016) is the one untried candidate in the window. It is not in haar_sym's group families
  (the field-automorphism semidirect product would need code), and PSL(2,8) has 63 involutions, which is the same floor
  as psl 19 × 19. Not run.

What would move it (not done here): (a) a new group family in the window with small involution count and a
larger-than-random tail (SL(3,q)-type, PΓL(2,8)); (b) voltage / route-chart lifts (research/lifts/, BEAT_16_5_SQUAD.md),
a different program; (c) a k = 5 orbit method at (6,9), which SIZE_LAW and STRUCTURE §2.5 rule out for Δ = 6 with one orbit.

Compute used this round: 4 cores, about 2.5 hours wall clock, roughly 1.0·10⁹ orbit-pair evaluations (four full passes
of 2.3–2.6·10⁸ each, plus the slices and tail tests). No solution saved to research/frontier/sols/. The record stays at 127,296.

Note on the histogram: `hist cost 63` counts pairs that were fully evaluated above the bound (the early abort is checked
only at chunk boundaries). It is an artifact of the bin, not a result; zero-cost pairs are never aborted.

## Round 3 (job raise3-6-9, branch claude/raise3-d6d9-round3-54sygo): new families, screens, exhaustive

Record to beat: **127,296** (N = 63,648). A new record needs N ≥ 63,649. Starting point: round 2's notes and
`haar_sym` (its EXHAUST mode is brought over unchanged from claude/raise-d6d9-round2; no code change in this round).

### What round 3 did

1. **Screen of the untested groups in the window** (RANDORB = random orbit pairs, ORBIT="3 2 0", cost bins of 3,
   the same tool and calibration as round 2). The record group (sl 17×13) has 51 samples at cost ≤ 2 per 10⁶
   random pairs; the expected number of zero-cost pairs is about 1150× the count per 200k, which matches the
   round-2 exhaustive count. Groups tested this round (cost ≤ 2 count per 10⁶ unless noted):

| group | N | μ | sampled minimum | note |
|---|---|---|---|---|
| sl 17 × 13 (record, reference) | 63,648 | 29.7 | 0 | 51 at cost ≤ 2 |
| psl 11 × 97 | 64,020 | 31.2 | 18 | nothing below 18; exhaustive pass below |
| sl 11 × 49 (round 2 closed) | 64,680 | 34.1 | 14 | 16 at cost 12–14; exhaustive minimum 14 (round 2) |
| psl 11 × 103 | 67,980 | 51.6 | 12 | 17 at cost 12–14; |Fix| = 5 (see below) |
| pgl 11 × 49 (PGL twin of sl 11 × 49) | 64,680 | 34.1 | 8 (200k) | 3 at cost 6–8 per 200k, record has 106; 96 % of samples cost ≥ 90 |
| pgl 13 × 31 (PGL twin of sl 13 × 31) | 67,704 | 49.9 | 12 (200k) | no sample below 12 |
| pgl 9 × 91 | 65,520 | 38.0 | 30 (200k) | no sample below 30 |
| prod psl 5 × psl 13 (A5 × PSL(2,13), no cyclic factor) | 65,520 | 38.0 | 42 (200k) | no sample below 42 |
| prod psl 5 × psl 5 × Z19 (A5 × A5 × Z19) | 68,400 | 54.3 | 54 (2,000) | not sampled further |
| prod psl 3 × sl 3 × Z_p (A4 × SL(2,3) × Z223, Z229, Z241) | 64–69 k | 32–61 | ≥ 85,000 | degenerate (fix ≈ 17, almost nothing covered) |
| prod psl 3 × psl 5 × Z91 | 65,520 | 38.0 | 129,402 | degenerate (|Fix| = 719) |
| pgl 7 × 193, pgl 7 × 199, sl 7 × 199, psl 7 × 397 | 64.8–66.9 k | 35–45 | 90–324 (2,000) | small q, weak |
| sl 8 × 133, psl 9 × 193, pgl 9 × 97 | 67–70 k | 46–64 | 82–93 (2,000) | weak |

   Reading: every PGL-type group has a far thinner low-cost tail than its SL/PSL partner, and the products without a
   cyclic factor are not competitive either. The only groups with sampled minima close to the record's μ are
   psl 11 × 97 (18) and psl 11 × 103 (12), and they are the two remaining groups below.

2. **Plain (non-orbit) annealing calibration** (`haar_sym` without ORBIT, 120 s, one thread, ≈ 2·10⁶ evaluations each,
   about 17,000 evaluations/s on the 64k groups):

| group | N | μ | best cost after 2·10⁶ evaluations |
|---|---|---|---|
| sl 17 × 13 (record group) | 63,648 | 29.7 | 12 |
| psl 11 × 97 | 64,020 | 31.2 | 35 |
| sl 8 × 127 | 64,008 | 31.1 | 56 |
| psl 7 × 379 (no wide rows: 650 µs/eval) | 63,672 | 29.7 | 136 (1.8·10⁵ evaluations) |

   For comparison the orbit method reaches μ = 29.7 with about 6·10⁴ evaluations on the record group. A plain solve at
   μ ≈ 30 needs about 10⁹ evaluations on the usual extrapolation (STRUCTURE §3), roughly 4 cores × 5 h. Plain annealing is
   not a realistic route to 127,296 for this budget.

3. **Single orbit of size 6** (`ORBIT="6 1 0"`, one α-orbit as S, the untried k = 6 variant of §5's "one orbit" row).
   `haar_sym` only builds α of odd prime order: on sl 17 × 13 and psl 19 × 19 it stops with "no conjugation of order
   dividing 6 found". On pgl 11 × 49 and psl 11 × 97 it runs, but the samples are almost all degenerate (minimum
   58,548 to 66,480, nearly every vertex uncovered). Dead end.

4. **tpgl** (twisted PGL) does not run in orbit mode: "ORBIT: plain groups only".

### Exhaustive pass started: psl 11 × 97 (N = 64,020, μ = 31.2, |Fix| = 5, α = conj(mat(5,2,6,7)) × (z ↦ 35 z))

Command: `ORBIT="3 2 0" EXHAUST="p 4 15 <prefix>" haar_sym 6 9 1 1 8 /dev/null psl 11 97`, parts p = 0..3, four
processes.

**Result: no solution.** All four parts finished (21,338 orbits, 227,644,453 pairs in total, about 42 min per part):
`solutions=0` in every part. The histogram lists only the cost-63 bin, which holds pairs aborted above the bound of 15
(the artifact noted in round 2). So no pair scored below 15, and the exact minimum is at least 15. The 1M-sample
minimum was 18, so the full minimum is probably 18. psl 11 × 97 is closed. Logs: `runs/d6D9_r3/exh_psl_11_97_p{0..3}.log`.

### Exhaustive pass started: psl 11 × 103 (N = 67,980, μ = 51.6, |Fix| = 5, α = conj(mat(5,2,6,7)) × (z ↦ 46 z))

Same command with `psl 11 103`, prefix `runs/d6D9_r3/exh_psl_11_103`. 22,658 orbits, 2.567·10⁸ pairs, four parts.
The 1M-sample minimum was 12 (17 samples at cost 12–14). Its N is above the record's, so a solution there would be
a new record too.

**Result: no solution.** All four parts finished: 256,681,153 pairs in total (about 46 min per part), `solutions=0`
in every part. The minimum cost is **13** (4,896 pairs at cost 13, none below), so psl 11 × 103 is closed.
Logs: `runs/d6D9_r3/exh_psl_11_103_p{0..3}.log`.

### Conclusion of round 3

**No record. Every group in the window that the orbit method (ORBIT="3 2 0", f = 0) can reach is now closed.**
Exhaustive results for the groups of order 63,649 to 68,000:

| group | N | μ | pairs | minimum cost | verdict |
|---|---|---|---|---|---|
| sl 11 × 49 (round 2) | 64,680 | 34.1 | 2.32·10⁸ | 14 | no solution |
| psl 11 × 97 (round 3) | 64,020 | 31.2 | 2.28·10⁸ | ≥ 15 (sample 18) | no solution |
| psl 19 × 19 (round 2) | 64,980 | 35.4 | 2.35·10⁸ | 3 | no solution |
| psl 13 × 61 (round 2) | 66,612 | 43.7 | 2.47·10⁸ | 12 | no solution |
| sl 13 × 31 (round 2) | 67,704 | 49.9 | 2.55·10⁸ | 6 | no solution |
| psl 11 × 103 (round 3) | 67,980 | 51.6 | 2.57·10⁸ | 13 | no solution |

The PGL twins, the products without a cyclic factor and the small-q groups are far weaker in sampling (tables above), so
they are not expected to move this. Plain annealing is about 10⁹ evaluations short at μ ≈ 30, and the single-orbit
k = 6 variant is degenerate. Two routes are still open, and both need new code or a different program: a group
family with small involution count and a k = 3 fixed set that the existing families lack (SL(3, q)-type or
PΓL(2,8) × Z43, which is not in haar_sym's families), and voltage lifts over a small bipartite base with two or more
vertices per side (research/lifts, BEAT_16_5_SQUAD.md). I did not run either: the first needs a new group
implementation, the second is a different program. Recommendation to the coordinator: stop compute on this cell
with these methods, and assign an Opus session to one of the two open routes if the cell is still wanted.
