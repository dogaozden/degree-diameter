# Cell (9,9): raise the orbit-symmetric Haar record (job raise-9-9)

Branch: claude/raise-d9d9-record-4vxjz9. Record to beat: **3,499,776** (= 2·N_h, N_h = |PSL(2,7) × SL(2,7) × Z_31| =
1,749,888; k = 3, m = 3, f = 0, μ = 30.5; file research/frontier/sols/d9D9_prod_psl_7_sl_7_31_orb3f0_s1.txt). Table value
2,961,536; Moore bound 38,347,922.

## Method

Orbit search (research/structured/haar_sym.c, `ORBIT="3 3 0"`): the connection set S is three free orbits of an
automorphism α (conjugation by an element of order 3, times z ↦ r z on Z_n). Every candidate graph is a Haar graph over
G = Q × Z_n with 2|G| vertices, so a larger |G| is a new record as soon as its diameter check passes.

- Candidate groups: `tools/orb_screen.py 9 9 LO HI "3 3 0"` (groups with all prime factors of n ≡ 1 mod 3).
- Random-S statistics (`--samples 300`) rank the groups; the annealer decides.
- Runs: `THREADS=1`, `nice -n 5`, one job per core, through `tools/orbq.sh` (which re-checks each solution with
  build_haar2.py). Logs and solutions are in runs/raise-d9D9/.
- μ grows about 12 % per 1 % of |G| near here (elasticity 1 + W/N ≈ 12), so the reachable rungs are close together in |G|.

## Calibration

Record group at μ = 30.5 (random S, 300 samples, 3 s): min 42, p1 51, p10 96, median 203. Its annealing run (seed 1,
K 8, 3,300 s, one thread) reached cost 0 after 1.26·10⁶ evaluations, about 2.6 ms each.

## Screen of the window 1,749,889 ≤ |G| ≤ 1,800,000 (μ 30.5–42)

Full list: runs/raise-d9D9/screen_1p75_1p80.txt. Best by (p1+p10)/2, with μ and |Fix(α)|:

| group | |G| | 2N | μ | fix | min | p1 | p10 | median |
|---|---|---|---|---|---|---|---|---|
| sl 121 1 | 1,771,440 | 3,542,880 | 35.3 | 119 | 36 | 52 | 80 | 136 |
| prod sl 9 psl 17 1 | 1,762,560 | 3,525,120 | 33.2 | 161 | 46 | 57 | 94 | 210 |
| prod psl 9 sl 17 1 | 1,762,560 | 3,525,120 | 33.2 | 161 | 54 | 63 | 94 | 215 |
| sl 29 73 | 1,778,280 | 3,556,560 | 36.9 | 29 | 48 | 60 | 104 | 178 |
| prod sl 4 sl 31 1 | 1,785,600 | 3,571,200 | 38.8 | 89 | 46 | 64 | 100 | 194 |

Reference (the record group, μ 30.5): min 42, p1 51, p10 96, median 203.

## Runs

Wave 1 (3,000 s each, seed 1, K 8, 4 cores): sl 121 1; prod sl 9 psl 17 1; sl 29 73; prod sl 4 sl 31 1. Status below.

Wave 1 result (all four finished, none reached cost 0; each run ~0.5–1.0·10⁶ evaluations, 3,000 s):

| group | μ | best cost | evals |
|---|---|---|---|
| sl 29 73 | 36.9 | **8** | 1.02·10⁶ |
| sl 121 1 | 35.3 | 10 | 5.3·10⁵ |
| prod sl 9 psl 17 1 | 33.2 | 14 | 7.4·10⁵ |
| prod sl 4 sl 31 1 | 38.8 | 16 | 6.9·10⁵ |

Wave 2 (3,600 s each, 4 cores): sl 29 73 seeds 2 and 3; sl 121 1 seed 2; prod sl 9 psl 17 1 seed 2.

Wave 2 result (3,600 s each, seed 2 or 3, none reached cost 0):

| group | μ | seed | best cost | evals |
|---|---|---|---|---|
| sl 29 73 | 36.9 | 3 | **6** | 1.19·10⁶ |
| sl 29 73 | 36.9 | 2 | 8 | 1.23·10⁶ |
| sl 121 1 | 35.3 | 2 | 10 | 6.4·10⁵ |
| prod sl 9 psl 17 1 | 33.2 | 2 | 10 | 8.8·10⁵ |

Wave 3 (3,600 s each, started 09:57 UTC): sl 29 73 with ORBW=3 (seed 4); sl 29 73 with RESTART=1 (seed 5); sl 29 73 (seed 6);
prod psl 3 sl 13 67 (μ 31.8, the only group between the record and 1,762,560; its random-S min is 78–84, worse than the record's 42).

Wave 3 result (3,600 s each, none reached cost 0; started 09:57 UTC):

| group | μ | variant | seed | best cost | evals |
|---|---|---|---|---|---|
| sl 29 73 | 36.9 | RESTART=1 | 5 | **8** | 1.14·10⁶ |
| sl 29 73 | 36.9 | plain | 6 | 12 | 1.13·10⁶ |
| sl 29 73 | 36.9 | ORBW=3 | 4 | 18 | 1.12·10⁶ |
| prod psl 3 sl 13 67 | 31.8 | plain | 1 | 20 | 6.9·10⁵ |

Wave 4 (3,600 s each, started 11:55 UTC, the last planned hour): sl 29 73 with RESTART=1, seeds 7–10.

Wave 4 result (3,600 s each, RESTART=1, seeds 7–10, sl 29 73, finished 13:01 UTC): best costs 12, 14, 18, 12. None reached cost 0.

## Verdict (session stopped at about 6 h)

**Not raised.** The record stays at 3,499,776. No candidate with |G| above 1,749,888 reached cost 0.

What was tried: 16 annealing runs (3,000–3,600 s each, one thread, about 1.1·10⁶ evaluations per hour-long run) on
five group orders with μ from 31.8 to 38.8, all with k = 3, m = 3, f = 0:

- sl 29 73 (μ 36.9), 12 runs over seeds, RESTART and ORBW variants: best cost 6 (seed 3, 1 h). Its runs stay at cost 6–18;
  the trajectories flatten after about 0.5·10⁶ evaluations.
- sl 121 1 (μ 35.3), prod sl 9 psl 17 1 (μ 33.2), prod sl 4 sl 31 1 (μ 38.8), prod psl 3 sl 13 67 (μ 31.8): best costs 10, 10, 16, 20.

Why it stalled: the record's group (μ 30.5) had random-S minimum 42 and reached cost 0 after 1.26·10⁶ evaluations on
a lucky seed. Every group above it has a worse random-S minimum (36–516) and a larger |Fix(α)| (29–161), which the
notes in STRUCTURE.md §2–3 identify as the k = 3 wall. Going from 30.5 to 36.9 in μ is about +1 % in |G|, which is
small, but it reaches the regime where this method stops finding zeros within an hour.

Options not tried (for the coordinator): many more core-hours at μ 31–33 (the leader's stats are better there, but
no candidate exists between 1,749,888 and 1,755,936 besides prod psl 3 sl 13 67); the metacyclic / voltage route
(research/lifts/); k = 3 with f = 3, m = 2; and SL(3,q)-type centralizers (STRUCTURE.md §7.3, not implemented).

## Files

- Screen: runs/raise-d9D9/screen_1p75_1p80.txt (all candidates with |G| in [1,749,889, 1,800,000]).
- Logs: runs/raise-d9D9/w1*, w2*, w3*, w4_* (each with queue log and per-run log).
- No solution was found, so nothing was written to research/frontier/sols/.
