# raise-d6D10, round 3: notes (in progress)

Job "raise3-6-10". Record to beat: **524,160** (N = 262,080, prod sl 5 psl 7 x Z13, orbit k=3 m=2 f=0).
Round 1 (branch claude/raise-d6d10-haar-mrmqi7, research/squads/cells/raise-d6D10.md): psl 17 x Z109 (N = 266,832)
ended at cost 1 (one alpha-fixed element uncovered) in 11 of 14 runs, never 0.
Round 2 (branch claude/raise-d6d10-resume-7y2sy2, research/squads/cells/raise-d6D10-r2.md): DUMPFIX, FIXHIST,
ENDG one-orbit exhaustive scan at the floor (about 7.5e7 orbit evaluations). No zero. Suggested next: two-orbit moves
at the floor, or a route-chart / voltage lift.

## What round 3 checked first (so as not to repeat round 2)

1. Window screen (`tools/orb_screen.py 6 10 262081 290000 "3 2 0" --list --nmax 3000`): the candidates are the same
   as in rounds 1 and 2. Groups with mu <= 26 and small cyclic factor are already tested, except:
   - pgl 11 x Z199 (N 262,680, mu 24.2): PGL(2,11) has a Z2 quotient that alpha fixes.
   - psl 81 (N 265,680, mu 27.1): alpha is unipotent (char 3), centralizer about q.
   The rest of the window either has mu >= 30 (tails already worse than the record group in round 2) or a large
   cyclic factor (n >= 367) or a solvable factor whose abelian quotient alpha fixes (A4, SL(2,3)).
2. Other order-3 scaling r (AR = 63 instead of the default 45) on psl 17 x Z109: RANDORB 3000 samples give min 7,
   p1 24, p10 64 (default: min 9, p1 25, p10 64). No real difference. The orbit partition of Z_109 is the same for
   r and r^2, but the pairing with the G-part is not, so this is a different family. Not a lever.
3. The k = 5, one-orbit family (Delta = 1 + 5, S = {e} + one alpha-orbit) was already measured at (6,8): min 38 at
   mu 30 (median 7,860), so it is not pursued (STRUCTURE.md §5).

RANDORB is fast: 3000 random symmetric S on psl 17 x Z109 take 0.5 s on one thread.

## Experiments

### E1. Uniform random symmetric S (RANDORB), 1e6 samples each, one thread (about 6,400 samples/s)

RANDORB is uniform sampling of orbit pairs, not annealing, so it is an unbiased read of the tail. The histogram
bins are raw cost / 3. Raw cost counts an uncovered alpha-fixed element as 1 and an uncovered free orbit as 3.

| group | N | mu | fix | min | p1 | p10 | median | bin 0 (raw 0-2) | zero found? |
|---|---|---|---|---|---|---|---|---|---|
| prod sl 5 psl 7 x Z13 (record) | 262,080 | 23.6 | 17 | **0** | 17 | 40 | 293 | 33 | yes (control) |
| psl 17 x Z109 | 266,832 | 28.4 | 8 | 1 | 27 | 64 | 387 | 4 | no |
| psl 17 x Z109, AR=63 (1e6 not run; 3e3 only) | 266,832 | 28.4 | 8 | 7 | 24 | 64 | 405 | - | no |

Reading: the record group has about 8x more mass in bin 0 than psl 17, and it produces a zero within 1e6 samples.
psl 17 reaches raw 1 (one fixed element) about once per 2.5e5 uniform samples, which matches the annealing floor
of round 1 and round 2. The estimate P(zero) for psl 17 is about 1e-6 per sample (Poisson in the free orbits,
times the fixed-element factor), so 1e7 or more samples could give a zero. That is the test below.

### E2. Campaign: psl 17 x Z109, 3 x 1.5e7 uniform samples (seeds 21, 22, 23), about 40 min on 3 threads

Files: `scratchpad/camp_psl17_s2*.out` (RANDORB line at the end). A zero-cost sample is saved by haar_sym
(check_and_write) to `scratchpad/psl17_zero_s<seed>.txt` and then checked with build_haar2.py.

(result below when it finishes)

### E3. Screen of the other untested window groups, RANDORB 1e6 each (`scratchpad/screen.sh`)

psl 13 x Z241, sl 11 x Z199, pgl 11 x Z199, prod psl 5 psl 5 x Z73, psl 81, prod psl 5 sl 5 x Z37, psl 9 x Z733.
Zero-cost samples are saved as `scratchpad/scr_<tag>.txt`.

(result below when it finishes)
