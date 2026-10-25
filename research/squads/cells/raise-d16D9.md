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
