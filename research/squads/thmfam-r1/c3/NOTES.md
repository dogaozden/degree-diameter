# c3: integer lifts at Delta = 8 and 10 (alpha = conj by w, order 3)

- gen_int.py q m TOKENS: fixed letters I, W, V (= I, w, w^2) and integer orbit reps a:b:c:d in SL(2,Z); orbit {X, wXw^-1, w^2Xw^-2} over Z, reduced mod q.
- enum_box.py: SL(2,Z) entries in [-2,2] give 52 matrices, 13 alpha-orbit classes (sign-identified). Excluded the alpha-fixed ones (+-I, +-w, +-w^2).
- Full enumeration: Delta 8 = 3 fixed pairs x C(13,2) = 234 sets; Delta 10 = 3 fixed x C(13,3) = 858 sets. All 1092 valid mod 29 (stage 1).
- screen2.py: stage 1 q=29 for all; stage 2 q=41,53 for the top 40 per Delta; mean over 29,41,53. Output screen_all.json, screen2.log.
- top8.json: best 8 per Delta; run_full.sh: family_score --group psl --qrange 23 113 for the 8 + 4 random baselines per Delta (full_*.json, full_summary.txt).

Results (mean_excess over 22 primes in [23,113], lower is better):
- Delta 8: integer best 3.844 (I W + O(-2:-1:1:0), O(-1:-2:1:1)); integer range 3.84-4.16. Random baseline 3.21-3.44 (mean 3.30). Gap +0.55.
- Delta 10: integer best 3.396 (I + O(-2:-1:1:0), O(-1:-2:1:1), O(-1:-1:2:1)); integer range 3.40-3.81. Random baseline 2.72-2.81 (mean 2.76). Gap +0.64.
- Integer families with entries in [-2,2] do not beat random alpha-closed sets at either Delta.
