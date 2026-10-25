# Squad round d11D10-r2: preamble shared by every card

**Goal.** The largest bipartite graph with maximum degree 11 and diameter 10. Table (CombinatoricsWiki): 130,592,354.
Ours: 148,729,680 vertices (PSL(2,89) × Z211, k = 5). Every graph here is a Haar graph H(G,S), |S| = 11, 2|G| vertices.
**Main target of this round: G = PSL(2,243) × Z11, N = |G| = 78,917,652, i.e. 157,835,304 vertices (+6.1 %).**
Fallback targets: anything between 148.8M and 157.8M vertices.

## Method in brief

- `haar_sym` (built, do not rebuild it): `/home/user/degree-diameter/research/structured/haar_sym`, source
  `research/structured/haar_sym.c`. It searches for S invariant under an automorphism α of G (orbit-symmetric S).
  Usage: `ORBIT="k m f" [VAR=x ...] haar_sym 11 10 SECONDS SEED K OUTFILE GROUP n`, G = GROUP × Z_n.
  For our target GROUP is `psl 243` (GF(3^5) = GF(3)[x]/(x^5+2x+1), entries written as integers Σ c_i 3^i) and n = 11.
- ORBIT="k m f": S = {e} ∪ (f−1 α-fixed generators) ∪ (m α-orbits of size k), f + k·m = 11.
- α choices on psl 243 × Z11 (z ↦ AR·z on Z11):
  - `AFROB=j` (j = 1..4): Frobenius x ↦ x^(3^j) on matrix entries, order 5. With ORBIT="5 2 1" and AR=3 (default).
    Fix(α) = PSL(2,3), 11 elements + e.
  - `AFROB=j AFROBH="0 1 2 0" AR=2` with ORBIT="10 1 1": α = (conj by h = mat(0,1,2,0)) ∘ Frobenius^j, times z ↦ 2z.
    α has order 10, S = {e} ∪ ONE orbit of size 10, Fix(α) = 3 elements + e. `AFROBD=1` instead of AFROBH: conjugation
    by diag(1,−1) (an outer automorphism) after the Frobenius; Fix(α) = 1 element + e. Only one orbit: annealing has no local
    moves, so this mode is a random search (RANDORB below).
- Annealing output: progress lines `t=… evals=… cost=… best=…`, then `RESULT … best=<cost>`. best=0 = solved
  ("full diameter check: OK", "wrote OUTFILE"). cost = number of uncovered group elements (B side, distance ≤ 9).
  Env: `ORBW=w` (an uncovered α-fixed element weighs w), `RESTART=1`, `TARGP` (% targeted candidates, 70),
  `COOL` (20), `REHEAT` (150), `CKPT=<file>` (checkpoint/resume), THREADS unset (= 1).
- `RANDORB=m`: cost statistics of m random symmetric S (no search): `RANDORB … min= p1= p10= median= mean=` plus a
  histogram of cost/k. New this round: `RANDB=b` aborts a sample once its cost reaches b (counts it as b),
  `RANDSTOP=1` stops at the first cost-0 sample (written to OUTFILE after a full check); with RANDB a line
  `RANDORB progress <samples>, <count> below b` comes every 500 samples.
- Other groups: `psl p` / `sl p` (p prime) with ORBIT="5 2 1" (conjugation α, needs p ≡ ±1 mod 5 and n's primes ≡ 1 mod 5)
  or "3 3 2"; `pgl p`, `heis q`, `meta m k r`, `prod G1 G2` exist too (see the comment at the top of haar_sym.c).

## Numbers to plan with

- W = 1,111,111,111 words; λ = W/N; μ = N·e^(−λ) (Poisson mean of uncovered elements for random S).
  psl 243 × Z11: λ = 14.08, μ = 60.6. psl 89 × Z211 (our 148.7M): μ = 24.1.
- Clumps: uncovered elements come in α-orbits, so a search sees about μ/k clumps plus misses of elements with small
  orbits (an element with stabiliser of order t is missed with probability e^(−λ/t)).
- Measured on psl 243 × Z11 (this machine, single thread): one evaluation ≈ 0.31–0.37 s, 1.0–1.7 GB per process.
  k = 5 (AFROB=1..4): RANDORB-16 medians 71 / 65 / 56 / 65, minima 51 / 35 / 31 / 36. Anneal AFROB=3 seed 1: cost 15
  after 2,000 evaluations. k = 10 (AFROB=1, AFROBH): 40 samples: 8 degenerate (cost > 50M), the other 32 have a mean of
  9.5 clumps (cost/10), minimum 31; 200 more samples had none below 30.
- Our 148.7M solution (k = 5, PSL(2,89) × Z211, μ 24) took 609 evaluations; k = 5 runs at μ ≈ 30–50 stall at 1–2
  uncovered α-fixed elements.

## Machine rules (4 cores and 15 GB shared by 16 cards and the Opus session's 3 long runs)

- **Every heavy command goes through the gate**:
  `/home/user/degree-diameter/research/squads/d11D10-r2/gate.sh SECS CMD ARGS...`
  It waits for a free CPU slot (2 slots are yours, shared by all 16 cards), then runs CMD under
  `nice -n 10 timeout SECS`. Never run haar_sym, a checker or a long script outside the gate. Give SECS = haar_sym's
  SECONDS + 120 (setup and the final check), or about 1.2 × the expected time for RANDORB (0.4 s per sample + 15 s setup).
- Your card states your heavy budget in slot-minutes (seconds inside the gate / 60). Waiting time does not count.
  When the budget is used up, stop. The slots are scarce: prefer short, decisive experiments.
- Run gated commands in the background (Bash `run_in_background`) and read their logs; a foreground Bash call is cut off
  after 10 minutes. Prefix env vars with `env`, e.g.
  `gate.sh 400 env ORBIT="10 1 1" AFROB=2 AFROBH="0 1 2 0" AR=2 RANDORB=200 /home/user/degree-diameter/research/structured/haar_sym 11 10 60 5 8 /dev/null psl 243 11 > run.log 2>&1`
- If you change code: copy haar_sym.c into your card folder as haar_sym_<card>.c and build there with
  `gcc -O3 -march=native -fopenmp -o haar_sym_<card> haar_sym_<card>.c -lm`. Never edit files outside your folder.
- No `build_haar2.py` above 2M vertices. No git commands except read-only `git show`/`git log`. Write only inside your
  card folder `research/squads/d11D10-r2/<card>/`, plus your one scoreboard line.
- Name solution files `d11D10_<fam>_<q>_<n>_orb<k>_<tag>_s<seed>.txt` in your card folder.
- Before you reply, make sure none of your processes is still running (kill them if needed).

## Checking a solution (a score counts only if this passes)

- psl 243 (prime power): `gate.sh 900 /home/user/degree-diameter/research/squads/d11D10-r2/tools/haarcheck_pq FILE` and
  `gate.sh 900 /home/user/degree-diameter/research/squads/d11D10-r2/tools/pqcheck FILE` → last line `VALID …`.
- psl p (p prime): `gate.sh 900 /home/user/degree-diameter/research/structured/tools/haarcheck_psl FILE`;
  sl p: `gate.sh 900 /home/user/degree-diameter/research/structured/tools/hcsl FILE`.
- The Opus session re-checks every claimed solution with a second checker.

## Scoreboard (one line per card, when you finish)

Append ONE line of JSON to `research/squads/d11D10-r2/scoreboard.jsonl`:

    {"card": "A3", "idea": "<one line>", "code": "<path>", "command": "<exact best command>", "score": <vertices of your best VALID graph, 0 if none>, "valid": true|false, "best_cost": "<group, mu, lowest cost reached, evals>", "next": "<one line>"}

Then reply to the Opus session in at most 5 lines. **Time box: 40 minutes wall clock from your start**, waiting included.
