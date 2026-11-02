# a11: planner for (6..11,12) with large-k automorphisms, and its calibration

Card a11, round 1, raise-d12. Folder: research/squads/raise-d12/r1/a11/. No graph found (score 0).

## 1. Model and planner

- W = sum over odd j <= 11 of Delta (Delta-1)^(j-1); lambda = W/N; mu = N exp(-lambda) (as in the card and SIZE_LAW.md).
- Clump model as in the card: P(valid S) ~ exp(-mu/k - F), F = |Fix(alpha) in G| exp(-lambda/k). |Fix| counts the identity,
  which is the same convention as haar_sym's "fixed-point misses" line (its nb (NFIX+1) exp(-lam/k) term).
- Candidates: G = Q x Z_n, Q in {SL(2,32) (aut order 5), SL(2,128) (7), PSL(2,243) (5), PSL(2,3^7) (7), PSL(2,125) (3),
  PSL(2,343) (3), SL(2,512) (9 via x -> x^2, and 3 via the cube)} and PSL(2,p) with conjugation of order 5 or 7 (all p up to
  the window). n runs over all integers with N in [current, 1.10 current]. r of order dividing k is chosen to minimise
  gcd(r-1, n) (|Fix_Z| = gcd(r-1,n)). ORBIT "k m f" with f in {0,1,2}, d = f + k m.
- Script: a11/plan.py (run `python3 plan.py 12`), full output in a11/table_D12.md.

## 2. Ranked table (best 3 per cell by the model's score; N = 2 x vertices is not used, N = |G|)

| cell | rank | Q | alpha | k | n | N | gain | ORBIT k m f | r, fixZ | mu | mu/k | |Fix_G| | F | log P |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| (6,12) | 1 | PSL(2,19) | conj order 5 | 5 | 1381 | 4,723,020 | +0.85% | 5 1 1 | r=75, 1 | 11.5 | 2.31 | 10 | 0.75 | -3.06 |
| (6,12) | 2 | PSL(2,19) | conj order 5 | 5 | 1382 | 4,726,440 | +0.93% | 5 1 1 | r=89, 2 | 11.6 | 2.33 | 20 | 1.51 | -3.84 |
| (6,12) | 3 | PSL(2,19) | conj order 5 | 5 | 1402 | 4,794,840 | +2.39% | 5 1 1 | r=89, 2 | 14.2 | 2.84 | 20 | 1.57 | -4.41 |
| (6,12) | - | SL(2,32) | x->x^2 (5) | 5 | 151 | 4,943,136 | +5.55% | 5 1 1 | r of order 5, fixZ 1 | 21.5 | 4.29 | 6 | 0.51 | -4.80 |
| (7,12) | 1 | PSL(2,31) | conj order 5 | 5 | 2011 | 29,923,680 | +0.01% | 5 1 2 | r=798, 1 | 14.4 | 2.87 | 15 | 0.82 | -3.69 |
| (7,12) | 2 | SL(2,32) | x->x^2 (5) | 5 | 922 | 30,182,592 | +0.88% | 5 1 2 | r=351, 2 | 16.4 | 3.28 | 12 | 0.67 | -3.95 |
| (7,12) | 3 | PSL(2,29) | conj order 5 | 5 | 2462 | 29,987,160 | +0.23% | 5 1 2 | r=401, 2 | 14.9 | 2.97 | 30 | 1.64 | -4.62 |
| (8,12) | 1 | SL(2,128) | x->x^2 (7) | 7 | 71 | 148,888,704 | +4.82% | 7 1 1 | r=20, 1 | 27.8 | 3.97 | 6 | 0.66 | -4.63 |
| (8,12) | 2 | PSL(2,125) | x->x^5 (3) | 3 | 146 | 142,569,000 | +0.37% | 3 2 2 | r=81, 2 | 13.4 | 4.46 | 120 | 0.55 | -5.01 |
| (8,12) | 3 | PSL(2,125) | x->x^5 (3) | 3 | 147 | 143,545,500 | +1.05% | 3 2 2 | r=67, 3 | 15.1 | 5.02 | 180 | 0.85 | -5.87 |
| (9,12) | 1 | PSL(2,125) | x->x^5 (3) | 3 | 571 | 557,581,500 | +0.85% | 3 3 0 | r=109, 1 | 12.6 | 4.20 | 60 | 0.17 | -4.36 |
| (9,12) | 2 | PSL(2,125) | x->x^5 (3) | 3 | 577 | 563,440,500 | +1.91% | 3 3 0 | r=213, 1 | 15.3 | 5.09 | 60 | 0.18 | -5.27 |
| (9,12) | 3 | SL(2,128) | x->x^2 (7) | 7 | 281 | 589,263,744 | +6.58% | 7 1 2 | r=59, 1 | 34.3 | 4.90 | 6 | 0.56 | -5.45 |
| (10,12) | 1 | SL(2,512) | x->x^2 (9) | 9 | 14 | 1,879,041,024 | +1.23% | 9 1 1 | r=9, 2 | 13.0 | 1.45 | 12 | 1.49 | -2.93 |
| (10,12) | 2 | PSL(2,243) | x->x^3 (5) | 5 | 262 | 1,879,674,984 | +1.26% | 5 2 0 | r=53, 2 | 13.1 | 2.62 | 24 | 0.56 | -3.18 |
| (10,12) | 3 | PSL(2,131) | conj order 5 | 5 | 1661 | 1,866,930,780 | +0.58% | 5 2 0 | r=59, 1 | 11.4 | 2.29 | 65 | 1.48 | -3.77 |
| (11,12) | 1 | PSL(2,243) | x->x^3 (5) | 5 | 781 | 5,603,153,292 | +0.15% | 5 2 1 | r=5, 1 | 13.7 | 2.74 | 12 | 0.23 | -2.96 |
| (11,12) | 2 | SL(2,512) | x->x^2 (9) | 9 | 43 | 5,771,340,288 | +3.16% | 9 1 2 | r=6, 1 | 25.1 | 2.79 | 6 | 0.71 | -3.50 |
| (11,12) | 3 | PSL(2,179) | conj order 5 | 5 | 1951 | 5,594,648,580 | +0.00% | 5 2 1 | r=896, 1 | 13.3 | 2.65 | 90 | 1.70 | -4.35 |

Notes on the table: (a) SL(2,32) x Z151 row: r of order 5 with gcd(r-1,151)=1, as in the director probe.
(b) Cells (7..11,12) with SL(2,128), SL(2,512) and PSL(2,2187) are in the table but are not sampleable with haar_sym (section 4).
(c) Model rank is not reliable at k = 5 (section 3, finding 1); at k = 3 the model is within about 3x of the measured lower tail.

## 3. Calibration (RANDORB, haar_sym, THREADS=1)

Each row is one instance at D = 12, d = 6. "Clumps" = cost/k as printed by RANDORB.

| instance | sampling | mu | mu/k | F (tool) | model: expected zero-cost samples | samples | min | p10 | median | zero-cost hits |
|---|---|---|---|---|---|---|---|---|---|---|
| PSL(2,19) x Z1381, conj 5, "5 1 1" | symmetric | 11.5 | 2.31 | 0.75 | exp(-3.06)=4.7% -> ~28 of 600 | 600 | 186 (37 clumps) | 275 | 730 | 0 |
| PSL(2,19) x Z1381 | plain random S | 11.5 | - | - | - | 120 | 659 | 3256 | 21,493 | 0 |
| SL(2,32) x Z151, AFROB=1, "5 1 1" | symmetric (my 5-sample check) | 21.5 | 4.29 | 0.51 | 0.8% | 5 | 51 | 51 | 1101 | 0 |
| SL(2,32) x Z151 | symmetric, director's probe (brief) | 21.5 | 4.29 | 0.51 | 0.8% -> ~12 of 1500 | 1500 | 15 (3 clumps) | - | 172 | 0 |
| SL(2,32) x Z151 | plain random S | 21.5 | - | - | - | 400 | 34 | 55 | 145 | 0 |
| PSL(2,79) x Z19, conj 3, "3 2 0" (f = 0, the (6,12) record cell) | symmetric | 10.2 | 3.41 | 0.51 | exp(-3.41-0.51)=3.0% -> ~9 of 300 | 300 | 1 | 3 (p1) | 9 (p10) | 25 | 0 (cost 1 seen: 0 orbit misses, 1 fixed miss) |

Findings:
0. k = 3 is roughly consistent. PSL(2,79) x Z19 "3 2 0" (N = 4.68M, mu/k 3.4, F 0.51) has min cost 1 (one fixed-element
   miss, no orbit miss) and p1 = 3 in 300 samples. The model's expected count of cost <= 3 is about 10, so it is optimistic by
   about 3x at most. Zero cost was not reached, but the lower tail is close to the clump model, so the k = 3 family is the
   best calibrated.
1. The clump model fails at k = 5 on the PSL(2,19) instance. For PSL(2,19) x Z1381 it predicts about 28 zero-cost samples in 600; there
   were none, and the minimum was 37 clumps (the model's mean is 2.3). The director's SL(2,32) probe also gives no zero
   cost where the model expects about 12 of 1500.
2. Typical costs are far above mu. Median / mu: SL(2,32) symmetric 172/21.5 = 8; plain 145/21.5 = 7; PSL(2,19) symmetric
   730/11.5 = 63; PSL(2,19) plain 21,493/11.5 = 1,900. The plain-random median on PSL(2,19) x Z1381 is 30 times the symmetric
   one, so orbit symmetry helps a lot there even though the model cannot see it. The independent-word model
   (lambda = W/N) does not describe the random cost distribution, so mu cannot rank cells across groups.
3. Consequence for the planner: the ranking above is "same W/N law" arithmetic, not a measured success rate. The useful
   measurement is the lower tail of RANDORB (min, p1) on each candidate, and that needs about 1,000 samples per candidate.
   At 0.08 s per sample for N = 4.9M (SL(2,32) x Z151) that is 80 s; the wide-row path (PSL(2,19) x Z1381) takes 0.47 s.
4. k = 7 is not calibrated. The SL(2,128) x Z_n cells have N >= 1.5e8 in the windows (too big for haar_sym).
   Smaller D = 10 instances at k = 7 did not give mu in range (mu is 1e3-1e5 or about 0).

## 4. Memory and tool limits (for the director)

- haar_sym keeps about 18 bytes per group element, so the 150 MB cap allows N of about 8 million. Only the k = 5 instance
  near 4.9M (SL(2,32) x Z151) fits comfortably. Cells at N >= 30M (the (7..11,12) rows) need haar_big0 (N/2 bytes;
  bit-parallel, SL/PSL(2,p) x Z_n only; SL(2,2^e) is not covered by it).
- Runs at N = 4.7M: a 600-sample RANDORB took 281 s on the wide-row path, so keep RANDORB under about 100 s by sample count.

## 5. What to do next (for the director)

- Use the planner only to shortlist. Before any long run, measure the lower tail with RANDORB on the top 3 per cell (about
  1,000 samples each), and rank by min and p1 in clumps, not by log P.
- The most promising measured signal is orbit symmetry on groups where plain random S is bad (PSL(2,19) x Z1381: the
  symmetric median is 30 times lower than plain). A k = 5 search there may still be worth a few cells, since its min is
  186 at N = 4.7M and the model does not describe it.
