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

### E2. Campaign: psl 17 x Z109, 3 x 1.5e7 uniform samples (seeds 21, 22, 23): **no zero**

Result (RANDORB, 15e6 samples per seed, 4.5e7 in total, plus the 1e6 of E1 = 4.6e7):

| seed | min | bin 0 (raw 0-2) | bin 1 (raw 3-5) | bin 2 (raw 6-8) | zero found? |
|---|---|---|---|---|---|
| 21 | 1 | 35 | 356 | 984 | no |
| 22 | 1 | 40 | 366 | 1007 | no |
| 23 | 1 | 41 | 437 | 964 | no |

So raw cost 1 (one alpha-fixed element uncovered) occurs about 2.5e-6 per uniform sample, and raw 0 never occurred.
The record group (E1 control, 1e6 samples) gave bin 0 = 33 and a zero, so its bin-0 rate is about 14x psl 17's.
Reading: psl 17 x Z109 is not a cell where uniform sampling at this scale finds a solution. A zero would need
roughly 1e8 or more samples (about an hour on 4 threads), and the expected gain is small. Not done. The
annealing floor of rounds 1 and 2 and the uniform tail agree: psl 17 sits at raw cost 1 to 3.

### E3. Screen of the other untested window groups, RANDORB 1e6 each (`scratchpad/screen.sh`)

| group | N | mu | fix | min | p1 | p10 | median | bin 0 | zero? |
|---|---|---|---|---|---|---|---|---|---|
| prod sl 5 psl 7 x Z13 (record, control) | 262,080 | 23.6 | 17 | 0 | 17 | 40 | 293 | 33 | yes |
| psl 17 x Z109 | 266,832 | 28.4 | 8 | 1 | 27 | 64 | 387 | 4 | no |
| psl 13 x Z241 | 263,172 | 24.6 | 5 | 6 | 60 | 199 | 1607 | 0 | no |
| sl 11 x Z199 | 262,680 | 24.2 | 11 | 18 | 60 | 147 | 872 | 0 | no |
| pgl 11 x Z199 | 262,680 | 24.2 | 11 | 15 | 61 | 180 | 131340 | 0 | no |
| prod psl 5 psl 5 x Z73 | 262,800 | 24.3 | 8 | 4 | 34 | 128 | 2270 | 0 | no |
| psl 81 (alpha unipotent, char 3) | 265,680 | 27.1 | 80 | 7 | 31 | 59 | 204 | 0 | no |
| prod psl 5 sl 5 x Z37 | 266,400 | 27.9 | - | - | - | - | - | - | not finished (stopped) |
| psl 9 x Z733 | 263,880 | 25.3 | - | - | - | - | - | - | not run |

None of the untested groups beats the record group or reaches zero in 1e6 uniform samples. The record group is
the only group in the window with a zero at that scale. psl 81 has 80 fixed elements (large centralizer), as the
structure predicted.

### Tally for round 3

- Uniform samples taken: about 5.2e7 in total (psl 17 4.6e7; the five screens 5e6; record control 1e6).
- Solutions above 524,160: **none**. Nothing was added to research/frontier/sols/.
- Compute: about 40 minutes of 3 threads for E2, plus the screens (1 thread, about 25 minutes). Most of the wall
  time was waiting.

### Decision

I stopped here. Not because the cell is provably stuck, but because:
- The one candidate with a good orbit fit (psl 17 x Z109, mu 28.4) has no zero in 4.6e7 uniform samples and sits at
  raw cost 1 to 3 in every method tried (annealing rounds 1 and 2, uniform sampling round 3).
- Every other untested group in the window has a worse tail or a large cyclic factor, or fixes a small quotient.
- The alpha choice is essentially unique per group (one class of order-3 elements; the scaling r vs r^2 gave the
  same tail: min 7 vs 9), so the orbit family has no unexplored parameter in this window.

### Suggested next steps (not done)

1. A 1e8-sample uniform run on psl 17 x Z109 (4 threads, about 1 hour, `RANDORB=25000000` per thread with
   `out` set so a zero is saved). Expected value is low (no zero in 4.6e7), but it is the cheapest test left.
2. Route-chart or voltage lift (research/theorems/BEAT_16_5_SQUAD.md) for (6,10). The round-2 suggestion of an
   exhaustive two-orbit move at the floor is still open. It costs more than the one-orbit scan.
3. k = 5 with one orbit (Delta = 1 + 5) was measured at (6,8) only (min 38 at mu 30; STRUCTURE.md section 5). It was
   not run at (6,10).
