# Squad round d15D10-r1: shared rules (read first)

Goal of the job: beat bipartite (Δ, D) = (15,10), table 2,300,326,510 vertices. Opus already has a VALID-by-self-check
graph of 2,325,625,680 (SL(2,139) × Z433) and is running higher rungs (μ = 16–18). Your card asks one question whose
answer helps Opus climb higher (bigger N = |G|, vertices = 2N).

Tool: `research/lowmem/haar_lean` (already built; source haar_lean.c, read its header comment and README.md there).
  Usage: `haar_lean d D seconds seed K outfile sl|psl p n` (G = SL(2,p) or PSL(2,p) times Z_n, p prime, gcd(p,n)=1).
  Env: `ORBIT="k m f"` (default for d=15: "3 5 0" = 5 free orbits of an automorphism alpha of order 3), `RANDORB=m`
  (print cost statistics of m random symmetric S, no search), `TARGP`, `ORBW`, `RESTART`, `COOL`, `REHEAT`, `TMIN`, ...
  Cost = number of group elements not covered; 0 = diameter <= D. mu = N exp(-W/N) is the Poisson difficulty
  (research/frontier/SIZE_LAW.md); the orbit method's effective difficulty is about mu/3 (research/structured/STRUCTURE.md).
  `research/lowmem/mu_list.py d D LO HI [k] [NMAX]` lists SL/PSL(2,p) x Z_n with N in [LO,HI] and their mu.

Machine (4 cores, 16 GB) is shared with 3 long Opus searches and a checker. So:
  - Big runs (N > 10^8, e.g. every (15,10) run) MUST go through the lock, one at a time for the whole squad:
      `flock /tmp/claude-0/squad-heavy.lock timeout 300 nice -n 10 <command>`
    Keep each big command short (RANDORB=12..20 takes ~15-40 s at N ~ 1.2e9, one sample ~1-2 s).
  - Small runs (N < 2*10^7, e.g. (15,8) proxies) need no lock: `timeout 300 nice -n 10 <command>`, at most one at a time per card.
  - THREADS=1 (the default). No git commits. Write only inside your card folder research/squads/d15D10-r1/<card>/.
  - Time box: about 15 minutes of wall clock for the whole card.
Output: append ONE json line to research/squads/d15D10-r1/scoreboard.jsonl (use `>>`, one line, valid JSON):
  {"card": "c5", "idea": "<one line>", "code": "<path or ->", "command": "<exact best command>", "score": <number>,
   "valid": true|false, "next": "<one line>"}
  plus a short results.txt in your folder (one line per run: group, mu, settings, numbers). Reply to Opus in at most 5 lines.
If a run writes a solution file with cost 0, keep it in your folder and say so (valid = true means haar_lean's own full
check passed; Opus re-checks independently).
