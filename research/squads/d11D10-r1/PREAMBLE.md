# Squad round d11D10-r1: preamble shared by every card

**Goal.** The largest bipartite graph with maximum degree 11 and diameter 10. The table (CombinatoricsWiki, read
2026-10-24) has 130,592,354 (Eyal Loz). Ours so far: 142,235,400 vertices (PSL(2,149) × Z43, k = 3) and 131,127,360
(SL(2,79) × Z133). Every graph here is a Haar graph H(G,S) with |S| = 11 and 2|G| vertices.

## The method in five lines

- `haar_sym` searches for S that is invariant under an automorphism α of G of prime order k (orbit-symmetric S).
  Built binary: `/home/user/degree-diameter/research/structured/haar_sym`. Source: `research/structured/haar_sym.c`.
- Usage: `ORBIT="k m f" [VAR=x ...] haar_sym 11 10 SECONDS SEED K OUTFILE GROUP... n`, G = GROUP × Z_n, GROUP is
  `sl p` or `psl p` (p prime; prime powers and `pgl` exist in haar_sym but have no low-memory checker yet).
  - `ORBIT="5 2 1"`: S = {e} ∪ two α-orbits of size 5 (α = conjugation by an element of order 5, times z ↦ rz).
    Needs p ≡ ±1 mod 5 and every prime factor of n ≡ 1 mod 5.
  - `ORBIT="3 3 2"`: S = {e, t} ∪ three α-orbits of size 3. Needs every prime factor of n ≡ 1 mod 3.
  - K = candidates per annealing move (use 8). SEED = any integer.
- Output: a progress line about every 30 s (`t=… evals=… cost=… best=…`), then `RESULT … best=<cost> evals=…`.
  best=0 means solved: then "full diameter check: OK" and "wrote OUTFILE". cost = number of uncovered group elements.
- Env vars: `ORBW=w` (an uncovered α-fixed element weighs w; ORBW=5 solved the (11,8) cell), `RESTART=1` (reheats start
  from fresh orbits), `ALPHA=<index>` (conjugating element), `AR=<r>` (z-multiplier), `TARGP` (% targeted
  candidates, default 70), `COOL` (s per halving of T, 20), `REHEAT` (s without gain before reheat, 150),
  `CKPT=<file>` (checkpoint/resume), `LEVELS=n` (ball sizes per BFS level for the first n samples, with RANDORB).
  Keep THREADS unset (= 1).
- `RANDORB=m` (with ORBIT): cost statistics of m random symmetric S, no search. Prints
  `RANDORB … min= p1= p10= median= mean=` plus a histogram. About 0.1–0.3 s per sample at these sizes.

## Numbers to plan with

- μ = N·e^(−W/N), W = 1,111,111,111: the Poisson mean of uncovered elements for random S. Bigger N = bigger μ = harder.
  μ ≈ 2.7 at the table, 11.7 at 142.2M vertices, 24.5 at 148.9M, 28 at 150M, 34 at 152M, 45 at 154.6M, 52 at 156M.
- μ_A ≈ μ/k + (fixed-point term): the expected number of uncovered α-clumps. The search effort grows like e^(μ_A/2):
  about 10⁵·e^((μ_A − 13)/2) evaluations to solve, give or take ×5. So k = 5 is the hope at large μ.
- Candidate groups (p prime only), with μ and μ_A: `research/squads/d11D10-r1/candidates_k5.txt` and
  `candidates_k3.txt`. Columns: vertices fam q n k f sym fix mu phi mu_A margin evals hours (evals/hours are optimistic).
- Measured here, single thread, N ≈ 75M: k = 3 ≈ 0.09 s per evaluation, k = 5 ≈ 0.25 s, about 1.4 GB per run.
  psl 149 × Z43 (μ 11.7, k = 3) solved in 89 evaluations; sl 79 × Z151 (μ 24.5, k = 3) was at cost 3 after 2,500;
  psl 101 × Z151 (μ 48.6, k = 5, ORBW = 5) at cost 11 after 900.

## Machine rules (4 cores and 15 GB shared by 16 cards and the Opus session)

- **Every heavy command goes through the gate**:
  `/home/user/degree-diameter/research/squads/d11D10-r1/gate.sh SECS CMD ARGS...`
  It waits for a free CPU slot, then runs CMD with `nice -n 10 timeout SECS`. Never run haar_sym, a checker or any
  long script outside the gate. Give the gate SECS = haar_sym's SECONDS + 120 (setup and the final check).
- Your card states your heavy budget in slot-minutes (seconds inside the gate / 60). Time spent waiting for a slot
  does not count. If your budget is used up, stop.
- Run gated commands in the background (Bash `run_in_background`) and read their logs; a foreground Bash call is cut
  off after 10 minutes. Prefix env vars with `env`, e.g.
  `gate.sh 720 env ORBIT="5 2 1" ORBW=5 /home/user/degree-diameter/research/structured/haar_sym 11 10 600 1 8 OUT.txt psl 71 421 > run.log 2>&1`
- No `build_haar2.py` above 2M vertices (it needs > 7 GB). No git commands except read-only `git show`/`git log`.
  Write only inside your card folder `research/squads/d11D10-r1/<card>/`, plus your one scoreboard line.
- Name solution files `d11D10_<fam>_<p>_<n>_orb<k>_<tag>_s<seed>.txt` in your card folder.
- Before you reply, make sure none of your processes is still running (kill them if needed).

## Checking a solution (a score counts only if this passes)

- PSL: `gate.sh 900 /home/user/degree-diameter/research/structured/tools/haarcheck_psl FILE` → last line
  `VALID d=11 D=10 group=psl … vertices=…`.
- SL: `gate.sh 900 /home/user/degree-diameter/research/structured/tools/hcsl FILE` → `VALID …`.
- Each takes 1–2 minutes at 150M vertices. The Opus session re-checks the best lines with a second checker.

## Scoreboard (one line per card, when you finish)

Append ONE line of JSON to `research/squads/d11D10-r1/scoreboard.jsonl`:

    {"card": "A3", "idea": "<one line>", "code": "<path>", "command": "<exact best command>", "score": <vertices of your best VALID graph, 0 if none>, "valid": true|false, "best_cost": "<group, mu, lowest cost reached, evals>", "next": "<one line>"}

Then reply to the Opus session in at most 5 lines. **Time box: 40 minutes wall clock from your start**, waiting included.
