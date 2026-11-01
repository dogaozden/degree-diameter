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
