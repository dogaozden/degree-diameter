# raise-d11D8, round 2: beat 2,258,520 at (Δ, D) = (11, 8)

Job "raise2-11-8" (Haiku worker, cloud session, started 2026-10-25 ~14:58 UTC; budget 6 h).
Record to beat: 2,258,520 = 2·|PSL(2,59) × Z_11| (N = 1,129,260), `research/frontier/sols/d11D8_psl_59_11_orb5_ORBW5_s3.txt`.
Round 1 (branch `claude/raise-d11d8-record-b63gz5`, `research/squads/cells/raise-d11D8.md` there) found nothing above
the record: psl 19 × Z331 (8 runs, best cost 5), sl 16 × Z281 (2 runs, best 21). Nothing from round 1 is repeated here.

## What round 1 left open, and what this round checked

1. **Other α for psl 19 × Z331.** Checked: the order-5 automorphisms of PSL(2,19) × Z_331 of the form
   (conj by an order-5 element) × (z ↦ r z) are exhausted by the four residues r ∈ {64, 124, 150, 323}, because the
   two conjugacy classes of order-5 elements in PSL(2,19) (x and x²) give (A, r) and (B, r) = (A, r³)². RANDORB with
   400 samples gives the same statistics for all four (min 32–37, p1 47–49, median 116–117). So there is no extra
   freedom in α for this group; the only remaining lever is the search.
2. **Random-sample mixing of the candidate groups** (RANDORB, 400 samples, ORBW=5, μ = raw Poisson mean):

   | group | N | μ | fix | min | p1 | p10 | median |
   |---|---|---|---|---|---|---|---|
   | psl 59 × Z11 (record) | 1,129,260 | 60.2 | 29 | 19 | 28 | 53 | 95 |
   | psl 19 × Z331 | 1,132,020 | 61.8 | 9 | 37 | 47 | 75 | 117 |
   | sl 16 × Z281 | 1,146,480 | 70.9 | 14 | 52 | 71 | 98 | 171 |
   | psl 11 × Z1721 | 1,135,860 | 64.1 | 4 | 76 | 105 | 176 | 485 |

   The record group mixes best, and psl 19 × Z331 is next. Everything else in the window is worse or fails the
   α-fixed-point test (no element of order 5 in Q, so Fix contains all of Q).
3. **k = 11, m = 1, f = 0 (one orbit of size 11).** Ruled out for this window: an order-11 automorphism needs
   11 | |Q|, which leaves PSL(2,q) with q ≡ ±1 mod 11 and n with primes ≡ 1 mod 11; there is no candidate of order
   near 1.13M whose centralizer is small. Rough first-moment estimate: N/11 ≈ 10⁵ orbits, expected completions
   ≈ 10⁵·e^(−ε·(μ/11 + |Fix|·e^(−λ/11))) with |Fix| ≥ 10 gives ≪ 1.
4. **New search mode: EXH (exhaustive one-slot scan).** Added to `research/structured/haar_sym.c`, opt-in, default
   path unchanged. When the raw cost is ≤ EXHT (default 5), it tries every orbit representative for one orbit slot
   with the other slot fixed (exact early abort against the best energy), moves to the best energy, and writes any
   cost-0 result through the existing checker. Runs at most once per EXHGAP seconds (default 1200). Prints one
   `EXH slot j: candidates, cost a -> b` line per scan.
   - Sanity check, (7,8) on psl 19 × Z14 (`ORBIT="3 2 1"`, 300 s, seeds 1–4): default 2/2 solved (6.9 s, 26.8 s);
     EXH 3/4 solved (0.6 s, 7.3 s, 18.5 s), the 4th still running at 30 s when its run ended. Solutions verified by
     haar_sym's full check. (A first EXH comparison used the stale binary and is discarded.)

## Round-2 runs on psl 19 × Z331 (N = 1,132,020, 2N = 2,264,040 would be a record)

Command: `ORBIT="5 2 1" ORBW=5 K=8 THREADS=1 EXH=1 EXHT=10 EXHGAP=900 ./haar_sym 11 8 16000 <seed> 8 <out> psl 19 331`
(binary `haar_sym_exh`, built from the same source), seeds 11–14, 16000 s each. Logs: `runs/raise11_8_r2/`.
Each solution, if one appears, goes to `research/frontier/sols/d11D8_psl_19_331_orb5_EXH_s<seed>.txt` and must pass
`build_haar2.py` (N ≤ 20M) before it counts.

## Log

- 14:58 UTC: session start. Read round-1 notes and STRUCTURE.md §7–8. Candidate list via `orb_screen.py --list`.
- ~15:03 UTC: built `haar_sym` and `tools/haarcheck_psl`.
- ~15:08 UTC: α variants (AR) checked on psl 19 × Z331; statistics identical.
- ~15:20 UTC: EXH implemented; (7,8) sanity check as above.
- ~15:25 UTC: four EXH runs started on psl 19 × Z331 (seeds 11–14, 16000 s each).

## Status

Running. No solution above 2,258,520 yet.
