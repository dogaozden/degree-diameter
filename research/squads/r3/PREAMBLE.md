# Squad round 3 preamble

Same tools, rules and report format as rounds 1 and 2: read `/home/user/degree-diameter/research/squads/r1/PREAMBLE.md`
(D = 5 notes, tools, machine rules) and skim `/home/user/degree-diameter/research/squads/r2/PREAMBLE.md` (D ≥ 7 notes).
Files only under `/home/user/degree-diameter/research/squads/r3/<your card>/`. One heavy process at a time, under
`timeout 900 nice -n 10`. About 45 minutes in total. No git, no edits elsewhere, nothing left running when you return.

## What rounds 1–2 taught (use it)

- The annealer reaches its plateau within ~60 s and then does not move; a plateau is a property of (group, α), not of
  run length. So **breadth over groups and over α (the conjugating element) beats long runs**. Runs of 120–300 s are
  enough to rank a choice; only rerun choices that reached ≤ 5.
- The minimum over random symmetric samples (`RANDORB=m`) predicts where annealing stalls.
- Choosing α: haar_sym prints `alpha: conj by <element> (index I)`. Set `ALPHA=I` to force a conjugating element, and
  `AR=r` for the multiplier on Z_n. Different α give different |Fix(alpha)| and different plateaus. A fast way to sweep:
  for I in a list of indices, run `ALPHA=$I ORBIT="..." RANDORB=20000 timeout 120 $B/haar_sym d D 1 1 8 /dev/null GROUP n`
  and read `|Fix(alpha)|` and `min=` from the output (if it says the conjugation has the wrong order, skip that I).
  Indices run from 0 to |Q|−1 (Q = the group without the cyclic factor).
- **The prize is (10,5)**: a cell we do not hold. Table 4,000 vertices, so N ≥ 2001. Best so far: 4 uncovered on
  A4 × SL(2,3) × Z7 (`prod psl 3 sl 3 7`, N = 2016, μ = 51.8, ORBIT="3 3 1", default α index 142, |Fix| = 17, seed 1,
  600 s); the same with ORBW=3 seed 2: 8. SL(2,13) (N = 2184): 6. PSL(2,7) × Z13: 8. A4 × PSL(2,7) (`prod psl 3 psl 7 1`,
  N = 2016): 9. Plain annealing without symmetry on A4 × PSL(2,7): 28.
- Other near misses: (8,8) N = 120,960 on `prod psl 7 sl 9 1` with ORBIT="2 4 0": 7, 8, 10 (three seeds; record
  N = 119,952). (6,8) N = 16,128 on `prod psl 3 psl 7 8` with ORBIT="2 3 0": 5 in five runs (record N = 15,840).
