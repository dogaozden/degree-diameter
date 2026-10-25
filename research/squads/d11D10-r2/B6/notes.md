# B6: does the k = 10 cost depend on the class of the orbit generator?

**Status: no sample was measured.** The job never ran a single haar_sym_B6 evaluation, so the per-class table is empty.
Wrapped up on the coordinator's instruction (13:38 UTC, past the 40-minute box, no new heavy runs).

## Commands

- `cp /home/user/degree-diameter/research/structured/haar_sym.c /home/user/degree-diameter/research/squads/d11D10-r2/B6/haar_sym_B6.c`
- Patch (in B6/haar_sym_B6.c only):
  1. `random_orbit()`: `B6CODE = -1` keeps the original draw (x uniform in G, same random sequence). `c > 0`: x = (x_q, 1) with
     ord(x_q) = c. `c = 0`: x = (x_q, 0), a z = 0 orbit.
  2. RANDORB prints one line per sample: `B6 t cost kind tr ord code`. kind = 1 if the orbit has a z = 1 element (x1 = its
     Q-part), 0 for a z = 0 orbit. tr = trace of x1 up to sign, as the field integer min(t, -t). ord = order of x1 in PSL(2,243).
  3. Env `B6STRAT="c1,c2,..."` cycles the class codes over the samples (0 = z = 0 orbits).
- Build, through the gate: `gcc -O3 -march=native -fopenmp -Wall -o haar_sym_B6 haar_sym_B6.c -lm`. It compiles with the
  existing -Wmisleading-indentation warnings only (log: B6/build.log). Runtime of the new code is untested.
- Job (one gate slot, `gate.sh 900 bash B6/run_all.sh`, log B6/run_all.log): build OK at 12:58:30. Then smoke (RANDORB=6),
  uniform (RANDORB=150, seed 6) and stratified (B6STRAT="2,3,11,61,121,122,0", RANDORB=140). All three failed at once with
  rc=127: `COMMON='ORBIT=10 1 1 AFROB=1 AFROBH=0 1 2 0 AR=2'` was used unquoted in `env $COMMON`, so the words "1", "2", "0"
  became the command for env (`env: '1': No such file or directory`, see B6/smoke.log, run_uniform.log, run_strat.log).
  Slot time used: a few seconds.
- The intended uniform command was `env ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=150 .../haar_sym_B6 11 10 60 6 8 /dev/null psl 243 11`.
- B6/analyze.py parses the `B6` lines and prints per-class means (degenerate fraction, mean/median cost, cost/10 of the
  non-degenerate samples). It has not been run on data.

## Per-class table (mean cost by class)

No data. Every row is n = 0.

| class (order of x1 in PSL(2,243), or z = 0 orbit) | n | mean cost | degenerate (cost > 1e6) |
|---|---|---|---|
| ord 2 (involutions, trace 0) | 0 | not measured | not measured |
| ord 3 (unipotent, trace +-1 after sign) | 0 | not measured | not measured |
| ord 11 | 0 | not measured | not measured |
| ord 61 | 0 | not measured | not measured |
| ord 121 | 0 | not measured | not measured |
| ord 122 | 0 | not measured | not measured |
| z = 0 orbit | 0 | not measured | not measured |

## Expected class mix of uniform RANDORB draws (derived by hand, not measured)

PSL(2,243) (|Q| = 7,174,332) has split tori of order 121 (29,646 of them) and nonsplit tori of order 122 (29,403). Element
counts: order 2: 29,403; order 3: 59,048; order 11: 296,460; order 61: 1,764,180; order 121: 3,261,060; order 122: 1,764,180.
Orders 244 (in the card's list) do not occur in PSL(2,243); 244 is the nonsplit torus order in SL(2,243).

Under uniform draws, about 1/11 of the accepted orbits are z = 0 orbits (every alpha_Q-orbit has size 10, see below). The
rest have x1 uniform in Q. Predicted shares of the samples:

| class | share of uniform samples |
|---|---|
| ord 121 | 41.3 % |
| ord 122 | 22.4 % |
| ord 61 | 22.4 % |
| ord 11 | 3.8 % |
| ord 3 (trace 1 up to sign) | 0.75 % |
| ord 2 (trace 0) | 0.37 % |
| z = 0 orbit | 9.1 % |

## Structural facts from the code (derived, not measured)

1. alpha_Q = conj(h) o Frob with h = mat(0,1,2,0) in SL(2,3). h has entries in GF(3), so conj(h) and Frob commute, and
   conj(h)^2 = id on PSL since h^2 = -I. So alpha_Q has order 10 and almost every Q-element has Q-orbit size 10. Hence the
   z = 0 orbits (x_q, 0) are accepted by orbit_of() with probability about 1/11 per uniform draw.
2. For such an S, all of S lies in Q x {0}. Every walk from (e,A) stays in cosets of Q x {0}. With the header's cost for
   D even (B-side elements not within D-1 of (e,A)), cost >= N - |Q| = 10N/11 = 71,743,320. This is a proof sketch, not a
   measurement. The degenerate cost of about 56M in the preamble is below this bound, so z = 0 orbits are a different
   degenerate group. They may be among the "cost > 50M" samples (8 of 40). Check: B6STRAT=0 with a few samples.
3. Annealing moves also call random_orbit(), so about 1/11 of their orbit proposals are z = 0 orbits with cost >= 71.7M.
   Unmeasured.

## Conclusion

Nothing has been measured, so no class is shown to be better, and no patch was made to sample a class. The run wrapper had a
quoting bug (AFROBH). The one property that looks worth checking first is point 2 above: whether the z = 0 orbits are a
separate degenerate group. Next step, when the cell is no longer waiting on compute: fix the quoting in run_all.sh,
run B6STRAT="0" for a few samples (expect cost >= 71.7M for each), then run B6STRAT="2,3,11,61,121,122" with 20 samples per
class and compare the means and degenerate fractions.
