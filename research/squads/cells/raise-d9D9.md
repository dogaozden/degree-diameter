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

(status updated as runs finish)
