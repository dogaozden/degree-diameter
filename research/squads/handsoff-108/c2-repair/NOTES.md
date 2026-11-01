# c2-repair (handsoff-108): two-move neighbourhood of the best known states

Card: `../cards.md`, section c2-repair. Seeds 108301-108399 (not used yet: the search is deterministic, no seeds).

## Tools
- `haar_c2.c` = copy of `research/d10D8/sym2/haar_sym2.c` plus `c2_twomove.inc` (included before `orbit_main`,
  called when `TWOMOVE=1`). Build: `gcc -O3 -march=native -fopenmp -o haar_c2 haar_c2.c -lm`.
- Run: `ORBIT="3 3 1" ORBW=3 TWOMOVE=1 TWOSTATE="<10 element indices, first = e>" C2K=100 C2M=2 C2SECS=3000
  ./haar_c2 10 8 1 1 8 /dev/null psl 23 97` (prod group: `prod psl 7 sl 8 7`, n = 7).
- Energy = raw uncovered + 2 * (uncovered alpha-fixed elements) (ORBW=3), as in the annealer.

## Moves (exact, no sampling)
1. single orbit replacement: every alpha-orbit of every slot (about N/3 per slot), the C2K best kept per slot;
2. pair of orbit replacements, slots a < b: all C2K x C2K pairs (distinctness checked);
3. right multiplication of two orbits by one alpha-fixed element c;
4. fixed letter e -> alpha-fixed c: all c ranked; the C2M best get moves 1-3 again.
The loop takes the best strictly improving move and restarts.

## Log

### 2026-10-31 23:0x-23:15 UTC: sanity run, energy-3 state (good_states line 2, psl 23 97), K=20, M=1
- Log: `sanity_e3a_K20.log`. Fix(alpha) = 11 non-identity elements (+e). N = 588984, ORBW=3 energy.
- Start energy 3. Single-slot scans (all ~196k orbits per slot): best = current orbit (energy 3); no other orbit below 3.
- Pairs of slots (20 x 20 each): none below 3; only the identity pair equal to 3.
- Right multiplication of two orbits by one alpha-fixed element: 33 tried, all energies >= 4.
- Fixed letter e -> alpha-fixed c: 11 letters, best energy 42 (c=6596). Its neighbourhood (M=1): best 4, none below 3.
- Result: no 2-move improves the state. Local optimum for moves 1-4. 727 s, 1.18M evals (about 1600 evals/s under nice).
- Scoreboard line written (first result, cost 3).

### Correction (23:26 UTC): the sanity run and the first driver attempt used ORBW=1 (raw count)
ORBW is read in orbit_main after the TWOMOVE hook. Fixed: c2_main now reads ORBW itself. The raw-count log is in
`raw_ORBW1_discarded/` (not the card's objective; its numbers are not used below). The sanity log `sanity_e3a_K20.log`
is also ORBW=1 (it said "ORBW=1" in its first line); its conclusion is only a raw-count statement.

### 23:26-23:41 UTC: energy-3 state line 2 (psl 23 97), ORBW=3, K=100, M=1 -> `run_e3_psl_a.log`
- Start energy 3 (ORBW=3). Singles: per slot the top-100 energies run from 3 (the state itself) to 30-33; no other orbit at 3.
- Pairs of slots (100 x 100 each): none below 3 (only the identity pair equals 3). 3 pairs, 30 000 pair evals.
- Right-mult pairs by one alpha-fixed c: 33 tried, all abandoned at bound E0+1 = 4 (all energies >= 4).
- Fixed letter: 11 alpha-fixed letters, best energy 42; best letter (c=6596) gets moves 1-3: pairs reach 4, none below 3.
- Result: exact local optimum for moves 1-4. 846 s, 1.24M evals.

### 23:41-23:53 UTC: energy-3 state line 3 (psl 23 97), ORBW=3, K=100, M=1 -> `run_e3_psl_b.log`
- Same picture as state line 2: singles top-100 energies from 3 (self) to about 30; pairs none below 3; right-mult all >= 4;
  fixed letter best energy 36 (c=357833), its pairs reach 4, none below 3.
- Result: exact local optimum for moves 1-4. 710 s, 1.24M evals. Neither energy-3 state moves.
