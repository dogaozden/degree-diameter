# Cell (Δ, D) = (9, 10): job raise3-9-10 (round 3, Haar worker)

Branch `claude/raise-d9d10-record-r3-wtimt3`.

## Record bar (discrepancy)

The brief says our record is 23,975,280. Round 1 (branch claude/raise-d9d10-record-7f9el2) claims a VALID record of
**24,099,600 vertices** (psl 151 × Z7, N = 12,049,800, research/frontier/sols/d9D10_psl_151_7_orb3f0_s1.txt,
sha256 d78ef086…c654), checked by haar_sym's full check and haarcheck_psl; the coordinator's check was pending.
This round aims for **N > 12,049,800** (vertices > 24,099,600), which also beats 23,975,280.

## Rounds 1 and 2 (do not repeat)

- Round 1: `3 3 0` (k=3, m=3, f=0) on psl 41×Z349, sl 43×Z151, psl 151×Z7 (solved), psl 79×Z49, prod sl 8×psl 19×Z7, sl 73×Z31 ORBW=3.
- Round 2 (notes: branch claude/raise-d9d10-record-r2-1792940825, research/squads/cells/raise-d9D10-r2.md): `3 3 0` on
  sl 73×Z31 (ORBW=3), pgl 73×Z31, psl 79×Z49 seed 5, prod sl 8×psl 19×Z7 (ORBW=3), psl 289×Z1. All stalled at cost 3
  after 0.7–1.3·10⁶ evals. Round 2 also screened every `3 3 0` group with N in (12,049,801, 12,200,000].
- Structured-search notes (STRUCTURE.md, branch claude/raise-d9d10-record-7f9el2, research/structured/): involutive α (k=2)
  creates word collisions (median cost 400–500 at μ 12.7 vs 31 for random S). k=5 at (11,8) solved with ORBW=5.

## Round 3: shapes not yet tried

Orbit shape = `k m f` with d = f + k·m, where f counts e when f ≥ 1 and f−1 fixed generators otherwise.

- `f ≥ 2` puts fixed generators inside C_Q(α), an abelian torus. Words in them collapse. Checked: `5 1 4` (k=5, f=4) on
  psl 59×Z121 (N 12,421,860, |Fix| 29): RANDORB min 650 raw uncovered (`3 3 0` calibration min ~13–33). Dropped.
  Shapes with f ≥ 2 are therefore not pursued at Δ = 9.
- `f ≤ 1` shapes (`3 3 0`, `4 2 1`, `2 4 1`, `8 1 1`) have no fixed generators. `4 2 1` (k=4, m=2, e included) allows
  Z_n factors ≡ 1 (mod 4), so groups that the k=3 filter excluded are now in range (e.g. psl 169×Z5, N 12,066,600).

## Screen (research/structured/runs/raise9-10-r3/screen/)

tools/orb_screen.py 9 10 12049801 12100000 "<shape>" --samples 150 --top 60, for 10 shapes; driver
runs/raise9-10-r3/screen_shapes.sh. Costs are raw uncovered counts. Early rows (150 samples):
- `4 2 1`: psl 169×Z5 min 25, p1 28, p10 55 (fix 83); psl 289×Z1 min 28 (fix 143).
- `3 3 0` (same samples): pgl 73×Z31 min 33–36, psl 79×Z49 min 33.

Full screen (10 shapes, same 150 samples; cost = raw uncovered elements; comparisons across k are rough):
- `3 3 0` best: psl 79×Z49 min 16 (fix 38); pgl 73×Z31 min 19; sl 73×Z31 min 18.
- `4 2 1` best: psl 169×Z5 min 25, p1 28, p10 55 (fix 83, μ/k 9.1); psl 289×Z1 min 28 (fix 143). Others ≥ 108.
- `2 4 1`, `2 3 3`, `2 2 5` (involutions, collisions): min 32 (`2 4 1`, psl 289×Z1) to 3810+. Dropped.
- `3 2 3`, `5 1 4`, `6 1 3`, `7 1 2` (fixed generators): min ≥ 33 but p1/p10 blow up; best fixed-gen shape is `3 2 3` pgl 73×Z31 (min 33, p1 39) — not pursued (same torus problem).
- `8 1 1`: psl 47×Z233 min 116. Dropped.

## Runs (round 3)

Shape `4 2 1` (k=4, m=2, e + two orbits of size 4), psl 169 × Z5, N = 12,066,600, μ 36.4, μ/k 9.1, |Fix(α)| 83.
Logs in research/structured/runs/raise9-10-r3/runs/.

- s1: plain, 12,600 s (started 02:08 UTC). t=241 s: cost 14 at 6.4e3 evals.
- s2: ORBW=4 (uncovered fixed element weighs k), 10,800 s (started 02:12 UTC).
- s3: RESTART=1, 10,800 s (started 02:12 UTC).
- s4: plain, 10,800 s (started 02:12 UTC). Finished 05:12 UTC: best 8 (280k evals), no solve.
- ORBW4 s2: finished 05:12 UTC, best 10 (energy 16), no solve (278k evals).
- RESTART s3: finished 05:12 UTC, best 5 (280k evals), no solve. Lowest cost of the round.
- s1: ends about 05:38 UTC; best 13 at 300k evals so far.
- RESTART s5, s6, s7 (started 05:13 UTC, 5,400 s each, RESTART=1, seeds 5–7).

Every run stayed at best cost ≥ 5 (raw uncovered orbit units: cost = uncovered/k). Round 1's psl 151×Z7 solve had cost 0
at 425k evals; no `4 2 1` run reached cost 0 in 230–300k evals. The plateau looks like the round-2 `3 3 0` plateau.
