# Squad round d15D10-r2: shared rules (read first)

Goal of the job: beat bipartite (Δ, D) = (15,10), table 2,300,326,510 vertices. Done: 2,325,625,680 (independently VALID)
and self-checked 2,454,528,720 and 2,467,618,800 (μ = 16.4, 18.2). Opus runs rungs at μ = 23.7, 27.5, 27.8 now; one
evaluation there costs ~1-2 s, and evaluations-to-solve grow roughly like e^(μ/4). Round 1 (research/squads/d15D10-r1/
and research/squads/LOG.md) found the defaults K=8, TARGP=70, ORBW=1, ORBIT "3 5 0" fine, alpha choice irrelevant,
k=5 a tie. Round 2 asks for ideas that cut evaluations-to-solve, tested on the cheap proxy (15,8)
SL(2,59) x Z43 (N = 8,828,760, mu = 23.0; ~0.01 s per evaluation; baseline solves in ~1,000-6,000 evaluations).

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
  - Small runs (N < 2*10^7, e.g. (15,8) proxies) go through one of two shared light slots (at most 2 squad proxy runs on
    the box at once): `research/squads/d15D10-r2/slot.sh timeout 120 nice -n 10 <command>` (it waits for a free slot).
  - THREADS=1 (the default). No git commits. Write only inside your card folder research/squads/d15D10-r2/<card>/.
  - Time box: about 15 minutes of wall clock for the whole card.
Output: append ONE json line to research/squads/d15D10-r2/scoreboard.jsonl (use `>>`, one line, valid JSON):
  {"card": "c5", "idea": "<one line>", "code": "<path or ->", "command": "<exact best command>", "score": <number>,
   "valid": true|false, "next": "<one line>"}
  plus a short results.txt in your folder (one line per run: group, mu, settings, numbers). Reply to Opus in at most 5 lines.
If a run writes a solution file with cost 0, keep it in your folder and say so (valid = true means haar_lean's own full
check passed; Opus re-checks independently).
