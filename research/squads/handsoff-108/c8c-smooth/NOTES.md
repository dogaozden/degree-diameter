# c8c-smooth notes (a smoother objective for the k = 3 annealer)

Started 2026-11-01 00:08 UTC. Card: cards.md "c8c-smooth". Seeds 108961-108999.

## Files
- `base.c` = research/d10D8/sym2/haar_sym2.c (unmodified), built as `haar_base` (gcc -O3 -march=native -fopenmp).
- `haar_smooth.c` = base.c + SMOOTHW (secondary term), built as `haar_smooth`.
- `ab_run.sh` = the A/B driver (baseline, then SMOOTHW=1; one heavy process at a time, nohup, nice 10).
- `ab_base.log`, `ab_s1.log` = CHAIN lines and progress; `ab_base.out`, `ab_s1.out` = RESULT lines.
- `gs/` = the stored good states evaluated with haar_smooth (secs = 0): G and F of each state (`gs/good_G.txt`).

## What SMOOTHW does (haar_smooth.c)
- D = 8 (even). The BFS from (e,A) to depth 7 gives the uncovered count u on the B side. G = N - lev[4] = N - |B-side
  ball of radius 5| (lev[4] is already computed by the BFS; cost_w/cost_fast return it as sec = G/N).
  F = G - u = number of B-side elements first reached at the last level (the card's F).
- Annealing energy in milli-units: Es = 1000*ce + SMOOTHW*(G - u - SMREF), ce = u + (ORBW-1)*fixmiss.
  In uncovered-element units that is ce + w*F/1000, the card's formula. SMREF = 0 (a constant shift does not change
  any decision: acceptance and argmin use differences only).
- Reported cost, CHAIN minima and the best state use the TRUE ce (ctrue[]). The annealer's acceptance and the
  candidate argmin use Es. Reheats restart from the best true state, as before.
- Early abort stays exact: with BMILLI=1 (set once the annealer starts) the bound is in milli-units and abort_lim()
  gives the uncovered count above which Es >= bound is certain: (1000-w) u + w (G - SMREF) >= bound (+1 milli slack).
  Checked: ABORT=0 and ABORT=1 give the same TRACE hash for SMOOTHW=1 and SMOOTHW=2 (3000 steps each).
- SMOOTHW=0 (or unset): the TRACE hash is identical to the unmodified binary (checked, 3000 steps, seed 108961).

## Measurements (ORBIT "3 3 1", psl 23 97, N = 588984)
- Random sets (RANDORB=1000, SMSTAT=1): G mean 528,387, sd 2,130, min 525,480, max 549,897. u mean 890 (heavy tail),
  corr(F, u) = -0.97 (F is mostly -u on random sets: the variation of u dominates).
- Stored good states (80 of the 119 in shared/good_states.tsv reload and reproduce their energies; 39 do not reload
  (they start from the fresh random start with u = 165), so they are left out): G mean 525,641, sd 293, range
  525,070-526,673. Energy-3 states: G 525,070-525,434. So good states sit at the LOW end of the random G distribution
  (the random minimum is 525,480): low G = large radius-5 ball = fewer short-word collisions.
- Scale: w = 1 gives a term of about 0.3 units (good states) to 2 units (random sets); one orbit is 3 units.
  w = 2 is comparable to one orbit. Card's tested values: 0.5, 1, 2.

## Runs
- A/B (ab_run.sh): haar_base seed 108961, then haar_smooth SMOOTHW=1 seed 108962. F15W3 schedule (COOL=15 REHEAT=30
  ORBW=3 RESTARTAFTER=0, K=8), VCLOCK=0.0032 s/step (= 312 steps/s, the free-core rate), MAXSTEPS=420000 (~60+ chains).
  Result tables below when the runs finish.

### Baseline arm (haar_base, seed 108961, 00:15-00:54 UTC): 29 chains, 3.35M evals
- chain minima (ORBW=3 energy): 9 (x1), 12 (x2), 15 (x6), 18 (x10), 21 (x8), 24 (x2). Median 18, mean 17.9, best 9.
- Compare with the reference in cards.md (median 18-21, P(min <= 9) about 1 in 15): consistent. So the step clock
  (VCLOCK 0.0032) reproduces the wall-clock schedule distribution.
- The run ended by MAXSTEPS = 420000 (about 14.5k steps and 116k evals per chain). Speed: 164 steps/s (1,300 evals/s)
  at about 50 % of a core: the box is oversubscribed (load 8 on 4 cores).
- Honest limit: 60 chains per arm was not reachable in the time budget (about 45 min per 29 chains at this load).

### Smoothing arm, SMOOTHW=1 (haar_smooth seed 108962, 00:54-01:31 UTC): 30 chains, 3.23M evals
- chain minima: 6 (x1), 12 (x1), 15 (x2), 18 (x14), 21 (x7), 24 (x5). Median 18, mean 18.9, best 6 (baseline best 9).
- Baseline (29 chains): 9 (x1), 12 (x2), 15 (x6), 18 (x10), 21 (x8), 24 (x2); median 18, mean 17.9.
- Mann-Whitney (summ.py ab_base.log ab_s1.log): P(base chain min > smooth) = 0.41, two-sided p = 0.25. No detectable
  difference. Chains <= 9: 1 of 30 (smooth) and 1 of 29 (base); <= 12: 2 of 30 and 3 of 29.
- Reading: with w = 1 the term is about 0.3-2 units, and the descents end in the same place. The one chain at 6 is
  one draw; it is not evidence of a better landscape.

### Extra arm, SMOOTHW=2 (ab_extra.sh, seed 108964, started 01:42 UTC, MAXSTEPS 240000 for the time budget)
- See the end of this file for the numbers when it finishes.
- Final (16 chains, 1.80M evals, ended 02:05 UTC): chain minima 12 (x2), 15, 18, 21 (median), 24. Median 21, mean 19.1,
  best 12. Mann-Whitney vs baseline (summ.py ab_base.log ab_s2.log): P(base > w2) = 0.38, two-sided p = 0.19.

## Mechanism check: G of the chain-minimum states (gchain/run_chain_G.sh, G_chain_min.txt)
- Reload of the CHAIN states works (u equals the logged chain minimum in every case).
- Mean G of the chain minima: baseline 525,744 (29 states); SMOOTHW=1 525,794 (30); SMOOTHW=2 525,780 (16).
  Mean raw u: 17.7 / 18.8 / 18.6. So the term did NOT pull the minima to lower G. The baseline descents already end
  at the low-G end (525.6k vs the random mean 528.4k): low G is a property of low-cost states, not a lever the
  secondary term adds.

## Verdict (round 1b, this card)
- Implemented and verified: SMOOTHW term, exact early abort (hash-equal ABORT=0/1 for w = 1 and 2), SMOOTHW=0
  trajectory identical to the unmodified binary.
- Measured: no detectable effect of w = 1 or w = 2 on the chain-minimum distribution at 16-30 chains per arm
  (medians 18 / 18 / 21 with baseline 18; best 9 / 6 / 12). Not the 60 chains per arm the card asked for: the box ran at
  about 50 % of a core (load 8), so one arm of 30 chains took 37-40 min.
- The card's scale: F = G - u is about 5.3e5 and varies by sd 2.1e3 across random sets, so w * F / 1000 with F not
  centred would add about 500 w units (it would also defeat the early abort). The implementation uses the
  SMREF-centred form (SMREF = 0 is a constant shift and changes no decision). Tested w = 1 and 2 only; w = 0.5 untested.

## Next (if someone continues this)
- A fragility statistic that is not G: the number of last-level elements covered by exactly one word (needs
  multiplicities in the last level; costs about 2x the last level). G alone is not it.
- More chains: 60 per arm needs about 2 h of one core at 300 steps/s, or a shorter schedule with a matched baseline.
