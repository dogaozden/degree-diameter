# Cell (14,10): raise the record (job raise-14-10, rounds 1-3)

Table value 1,213,477,190. Moore bound 22,976,415,308. Branch of this round: claude/raise-d14d10-record-3-hp5jbg.

## Current record (as of round 3 start)

**(14,10) >= 1,350,537,864** = 2N, N = 675,268,932 = |PSL(2,157) x Z_349|, orbit k=3, m=4, f=2, fix 77.
Solution: research/frontier/sols/d14D10_psl_157_349_orb3_s2_n1350537864.txt (round 2, VALID by haarcheck_psl).

The round-3 brief said 1,326,627,120 (the original record). That is out of date: round 1 raised it to 1,341,781,320
and round 2 to 1,350,537,864. Round 3 beats 1,350,537,864, i.e. any N > 675,268,932.

Rounds 1 and 2 (branches claude/raise-d14d10-record-2-b14g4 and claude/raise-d14d10-record-2-3vy08n) are summarized in
the "History" section below. Their logs and cell notes live on the round-2 branch under research/squads/cells/raise-d14D10/.

## Round 3 (job raise3-14-10, this branch)

Method: `research/structured/tools/orbq.sh` with `ORBIT="3 4 2"` (k=3, m=4 free orbits, f=2 fixed generators), seed 2
unless noted, `THREADS=2` (16 GB box: THREADS=4 OOM-killed at setup, THREADS=2 peaks near 13 GB RSS), one run at a time,
built with `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` (binary kept outside git).

Candidate screen: `tools/orb_screen.py 14 10 675268933 700000000 "3 4 2" --list --nmax 1000` (prime-q PSL and SL with
Z_n, every prime of n = 1 mod 3). The default --nmax 400 hides the low-fix candidates PSL(2,149) x Z_409 and
PSL(2,113) x Z_937, so round 3 used --nmax 1000. Prime-power q (GF(p^k), e.g. PSL(2,121)) is excluded: the low-memory
checker haarcheck_psl only handles prime q.

Why PSL: |Fix(alpha)| for conjugation by an element of order 3 is the torus centralizer, (q-1)/2 or (q+1)/2 in PSL
and about q in SL. Round 2 saw that low |Fix| solved faster at mu 27-30 (fix 77 solved at 2.9k evals; fix 140
stalled at cost 6 after 7.3k).

Queue (research/squads/cells/raise-d14D10/r3/jobs.txt), lowest mu first, then lowest fix:

| N | 2N | mu | group | fix | budget |
|---|---|---|---|---|---|
| 675,511,980 | 1,351,023,960 | 27.8 | PSL(2,131) x Z_601 | 65 | 5400 s, seed 2 |
| 675,944,304 | 1,351,888,608 | 28.1 | PSL(2,113) x Z_937 | 56 | 5400 s, seed 2 |
| 676,445,100 | 1,352,890,200 | 28.5 | PSL(2,149) x Z_409 | 74 | 5400 s, seed 2 |
| 677,736,396 | 1,355,472,792 | 29.5 | PSL(2,163) x Z_313 | 80 | 3600 s, seed 3 (seed 2 reached best cost 1) |

Not yet queued (for a later round): PSL(2,127) x Z_661 (N 676.9M, mu 28.9, fix 62), PSL(2,169) x Z_283 (33.8, 83),
PSL(2,151) x Z_397 (34.2, fix 74), PSL(2,139) x Z_511 (36.7, fix 67).

### Results (round 3)

(filled in as the queue runs; see research/squads/cells/raise-d14D10/r3/runs/ for logs)

- pending

## Round 2 summary (for reference)

- Start point 1,341,781,320 (round 1). Solved: PSL(2,157) x Z_349 (N 675,268,932, fix 77, 2,897 evals, THREADS=2).
- Tried above 670,890,660 and not solved: PSL(2,281) x Z_61 (best 6, 7,305 evals), PSL(2,163) x Z_313 (best 1,
  7,369 evals), PSL(2,181) x Z_229 (best 6, 3,609 evals).
- Not tried: PSL(2,241) x Z_97 (N 678.9M, fix ~119), and more seeds of PSL(2,163) x Z_313.

## History (rounds 1 and 2, condensed)

- Round 1 (claude/raise-d14d10-record-2-b14g4): from 1,326,627,120 to 1,341,781,320 (PSL(2,331) x Z_37, solved 641 evals).
  Intermediate solved: PSL(2,263) x Z_73 (1,327,956,432), PSL(2,163) x Z_307 (1,329,489,288), PSL(2,271) x Z_67
  (1,333,450,080). Unsolved stalls at cost 3: SL(2,151) x Z_193, PSL(2,199) x Z_169, PSL(2,169) x Z_277,
  PSL(2,257) x Z_79, PSL(2,173) x Z_259.
- Round 2: see above.

## Lessons

- At mu 20-22 the solves took 150-1,650 evals; at mu 24.5 PSL(2,331) x Z_37 took 641 evals with fix 164. So fix is
  not the only predictor: n matters too. Solved cases have n in {37, 67, 73, 307, 331, 349} and unsolved ones include
  n = 61, 79, 169, 229, 259, 277, 313 (the last at best cost 1).
- Each unsolved rung ends at cost 1-3 (one fixed point or one orbit uncovered), or 6-7 at high fix.
- One haar_sym run at a time: two at N ~ 6.8e8 are OOM-killed during the wide-rows setup.

## Verification

- Solutions are checked with `research/structured/tools/haarcheck_psl` (low memory, independent BFS from both sides;
  orbq.sh runs it automatically above 20M vertices). Record only after VALID d=14 D=10.
- The coordinator re-checks independently.
