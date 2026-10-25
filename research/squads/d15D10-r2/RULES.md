# Squad round d15D10-r2: shared rules (read first)

Goal of the job: beat bipartite (Δ, D) = (15,10), table 2,300,326,510 vertices. We hold 2,325,625,680 (independently VALID)
and self-checked 2,454,528,720 and 2,467,618,800, all with orbits of size k = 3 (ORBIT="3 5 0") on SL(2,p) x Z_n.

NEW IDEA OF THIS ROUND (Opus, 2026-10-25): orbits of size k = 5 (ORBIT="5 3 0": S = 3 orbits of an automorphism alpha of
order 5) on PSL(2,p) x Z_n. Model (research/structured/STRUCTURE.md section 1): the uncovered set comes in alpha-orbits, so
P(cost 0) ~ exp(-mu_eff) with mu_eff = mu/k + F, F = |Fix(alpha)| exp(-lambda/k), lambda = W/N ~ 17.6 at (15,10). For k = 3,
F is tiny but mu/3 is big; for k = 5, mu/5 is smaller but F = |Fix| * 0.03 matters, and |Fix| = (p -+ 1)/2 for PSL (p -+ 1
for SL), so small p helps (p ~ 60-150 gives F ~ 1-2). First data: at mu ~ 26, random symmetric S have median 6-7
"units" for k = 5 against ~11 for k = 3, and k = 5 annealing reaches cost 2-5 in ~250 evaluations where k = 3 sits at 10.
This round maps where k = 5 (and k = 15) works best.

Tool: `research/lowmem/haar_lean` (already built; source haar_lean.c, read its header comment and ../lowmem/README.md).
  Usage: `haar_lean d D seconds seed K outfile sl|psl p n` (G = SL(2,p) or PSL(2,p) times Z_n, p prime, gcd(p,n)=1).
  Env: ORBIT="k m f" (f + k m = 15), RANDORB=m (cost statistics of m random symmetric S, no search), LEVELS=1 (with
  RANDORB: one line per sample on stderr: ball sizes, cost, units), TARGP, ORBW, K is the 5th argument, AR (r on Z_n),
  ATRACE. Cost = number of group elements not covered; 0 = diameter <= D.
  RANDORB prints e.g. "RANDORB ... min=.. p10=.. median=.. mean=.. mu=.. time=.. units: min=.. p10=.. median=.. mean=.."
  where units = (uncovered free alpha-orbits) + (uncovered alpha-fixed points): the Poisson count whose P(0) matters.
  MEDIAN UNITS IS THE MAIN SCORE OF THIS ROUND (lower is better; compare at similar mu).
  Group lists: `cd research/lowmem && python3 klist.py 15 10 LO HI k [PMIN] [PMAX] [NMAX] 2300326510` lists SL/PSL(2,p) x Z_n
  usable with orbit size k (order-k element exists, all prime factors of n = 1 mod k), with mu, F, mu_eff, |Fix|, and the
  gain over the table. For the (15,8) proxy use `python3 klist.py 15 8 8.5e6 9.6e6 k`.

Machine (4 cores, 15 GB) is shared with 3 long Opus searches. So:
  - Full-scale runs ((15,10), N ~ 1.2-1.3e9, 0.31 GB, ~1-1.5 s per sample) MUST go through the heavy lock, one at a time
    for the whole squad:  `flock /tmp/claude-0/squad-heavy.lock timeout 300 nice -n 10 env ... ./haar_lean 15 10 1 SEED 8 /dev/null FAM P N`
    Keep each command short: RANDORB=24 takes ~30-45 s. At most 8 full-scale commands per card.
  - Proxy runs ((15,8), N < 2e7, ~0.01 s per evaluation) go through one of two shared light slots:
    `research/squads/d15D10-r2/slot.sh timeout 130 nice -n 10 env ... ./haar_lean 15 8 120 SEED 8 /dev/null FAM P N`
  - THREADS=1 (the default). No git commits. Write only inside your card folder research/squads/d15D10-r2/<card>/.
    Run commands from research/lowmem (cd there first), save raw output into your folder.
  - Time box: about 20 minutes of wall clock for the whole card (the lock may make you wait; that is expected).
Output: append ONE json line to research/squads/d15D10-r2/scoreboard.jsonl (use `>>`, one line, valid JSON):
  {"card": "c5", "idea": "<one line>", "code": "<path or ->", "command": "<exact best command>", "score": <number>,
   "valid": true|false, "next": "<one line>"}
  plus a short results.txt in your folder (one line per run: group, k, mu, F, the RANDORB numbers or evals-to-solve).
  Reply to Opus in at most 5 lines.
If a run writes a solution file with cost 0 (only when outfile is not /dev/null), keep it in your folder and say so.
