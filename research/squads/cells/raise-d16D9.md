# raise-d16D9: beat 337,394,400 vertices at (Δ,D) = (16,9)

Record held: Haar graph of SL(2,151) × Z49, |G| = 168,697,200, 2|G| = 337,394,400 vertices, k=3 orbit search
(ORBIT="3 5 1", |Fix α| = 149), found in 97 evaluations at μ = 14.4 (runs/d16D9_sl_151_49_orb3_s1.log).
Table value 288,939,118. Bar to beat: |G| > 168,697,200.

## Method
- Search: research/structured/haar_sym.c (orbit search, k=3, f=1, m=5), THREADS=1, 4 runs in parallel.
- Group choice: |G| = |SL(2,p)| · n with p prime, n odd with every prime factor ≡ 1 mod 3 (rule of STRUCTURE.md §2),
  |G| just above the bar. Enumerated by a short script (candidates sorted by excess over the bar).
- Excess is cheap at first: d ln μ / d ln N ≈ 1 + W/N ≈ 17 for this cell, so +1 % in |G| costs about +17 % in μ, and
  evaluations grow like e^(μ/4.5). Climb in small steps.
- Verification: build_haar2.py for ≤ 20M vertices is not used here (all graphs > 20M). Above 20M:
  research/frontier/haarcheck_sl.c (hcsl) and research/frontier/haarcheck2.c (hc2) for SL(2,p) × Z_n, both
  independently; both binaries built from those sources in the scratchpad.

## Ladder (|G| excess over the bar)
| group | |G| | excess | status |
|---|---|---|---|
| sl 79 × Z343 | 169,085,280 | +0.23 % | running (wave 1) |
| sl 89 × Z241 | 169,876,080 | +0.70 % | running (wave 1) |
| sl 107 × Z139 | 170,266,104 | +0.93 % | running (wave 1) |
| sl 103 × Z157 | 171,541,968 | +1.69 % | queued |
| sl 79 × Z349 | 172,043,040 | +1.98 % | queued |
| sl 83 × Z301 | 172,082,904 | +2.01 % | queued |

## Log
(see bottom; newest last)

- 2026-10-25 07:44 wave 1 (haar_sym, k=3 m=5 f=1, THREADS=1, K=8): sl 79x343 solved at 1625 evals (981 s); checked
  VALID by hcsl and hc2: 338,170,560 vertices (+0.23 % over 337,394,400). Saved research/frontier/sols/d16D9_sl_79_343_orb3_s1.txt.
- 2026-10-25 ~07:55 sl 107x139 solved at 2841 evals (1190 s); VALID by hcsl and hc2: 340,532,208 vertices (+0.93 %).
  Saved research/frontier/sols/d16D9_sl_107_139_orb3_s1.txt. Checker outputs: research/frontier/runs/raise_d16D9_checks.txt.
  Current best: 340,532,208 (sl 107 x Z139).
- Running: sl 103x157 (+1.69 %, cost 2 at 1,833 evals), sl 89x241 (+0.70 %, cost 2), sl 79x349 (+1.98 %), sl 83x301 (+2.01 %).
- Notes: stdout of haar_sym is block-buffered when redirected, so logs only show RESULT at exit; solution files appear directly.
- 2026-10-25 ~08:00 sl 89x241: no solve (best 2 after 2,225 evals, 1,800 s).
- 2026-10-25 ~08:05 sl 103x157 solved at 3,617 evals (1,715 s); VALID by hcsl and hc2: 343,083,936 vertices (+1.69 %).
  Saved research/frontier/sols/d16D9_sl_103_157_orb3_s1.txt. Current best: 343,083,936.
- Running: sl 79x349, sl 83x301 (cost 12 at ~500 evals), sl 109x133 (+2.09 %), sl 137x67 (+2.12 %).
- 2026-10-25 08:05-08:21: sl 137x67 solved at 361 evals (350 s), VALID hcsl+hc2: 344,542,944 (+2.12 %). Current best.
  sl 79x349 solved at 1,569 evals (1,083 s), VALID hcsl+hc2: 344,086,080 (+1.98 %). Both saved in research/frontier/sols/.
- Running: sl 83x301 (cost 12), sl 109x133 (cost 12), sl 101x169 (+3.2 %).
- 2026-10-25 08:30: sl 101x169 solved at 1,545 evals (1,188 s), VALID hcsl+hc2: 348,207,600 (+3.19 %). Current best. Saved.
  sl 83x301: no solve (best 12, 2,201 evals).
- Running: sl 109x133 (cost 6), sl 89x247 (cost 14), sl 83x307 (+2.2 % over 101x169), sl 97x193.
- 2026-10-25 08:42: sl 109x133 solved at 3,577 evals, |G| 172,224,360 (344,448,720 vertices). Below the current best, so not checked
  and not recorded. Kept only in the scratchpad.
- Running: sl 89x247 (cost 6), sl 83x307 (cost 14), sl 97x193 (cost 18), sl 239x13 (+5.2 %).
