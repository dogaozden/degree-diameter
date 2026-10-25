# Squad d16D10-r2: shared preamble (read this first)

Job "cell-16-10" (Opus researcher, cloud session, 2026-10-25). Goal: a bipartite graph of maximum degree 16 and
diameter 10 with as many vertices as possible. Table value (2013): 4,119,507,330. Ours so far: **4,386,127,200**
(Haar graph H(G,S), G = SL(2,151) × Z637, |G| = 2,193,063,600, checked). A Haar graph has 2|G| vertices.

This round works at the real target, not a proxy: **(Δ, D) = (16, 10) with |G| between 2.30e9 and 2.32e9**
(4.60–4.64 billion vertices, +12 % over the table, +5 % over our record). A run that reaches cost 0 there is a new
record candidate (Opus verifies it).

## What we know (Opus, this morning)

- S = {e} ∪ m orbits of an automorphism α of order k (ORBIT="k m f", 16 = 1 + k·m). α = (conjugation by an element
  g of order k) × (z ↦ r z on Z_n). Holes (uncovered elements) then come in α-orbits of size k, except at the
  **α-fixed elements**: (torus containing g) × {z = 0}, about p of them in SL(2,p), p/2 in PSL(2,p).
- A free hole orbit costs k; a fixed hole costs 1. Expected (random-like S): μ/k free hole orbits, plus
  |Fix|·e^(−λ/k) fixed holes, λ = W/|G| ≈ 17.9, μ = |G|·e^(−λ).
- Data at |G| ≈ 2.276e9 (μ ≈ 31): k = 3 on SL(2,151) × Z661 reached cost 10 in 29 evals, then stuck. k = 5 on the same
  group reached **cost 2 in 41 evals and stuck there for 170 evals: both holes are α-fixed** (torus, z = 0). k = 5 on
  PSL(2,61) × Z20071 (only 30 fixed elements): cost 20 after 73 evals (one run, noisy).
- So the questions are: which group shape (p small with n large, or p large with n small; SL or PSL), which k, which
  schedule. Each card tests ONE of these at the band above.

## The tool (already built; do not rebuild, do not edit)

    HB=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin/haar_big
    R=/home/user/degree-diameter/research/squads/d16D10-r2

Usage (run from your card folder `$R/cN/`):

    ORBIT="5 3 1" THREADS=1 $R/slot.sh cN timeout 660 nice -n 10 $HB 16 10 600 SEED 4 OUT.txt FAMILY P N > run.out 2> run.log

- arguments: d D seconds seed K outfile family p n. seconds = 600 (the wall-clock budget of the search), seed = any
  integer, K = 4 (candidates per step), outfile = a file in your folder, family = sl or psl, p prime, n the Z_n factor.
- **Every heavy run must go through `$R/slot.sh cN ...`**: it waits for one of the shared slots (only 2–3 heavy
  runs fit on this machine), then runs. Waiting can take 10–30 minutes; that is expected. Each run uses one core
  and ~1.3 GB.
- stdout (run.out): `RESULT d=16 D=10 group=... N=... vertices=... best=<cost> evals=<n> steps=<n> time=<s> ... mu=<μ>`.
  best = 0 means solved (it then writes OUT.txt). stderr (run.log): one line per step
  `t=... step=... evals=... slot=... cand=... cost=... best=... T=...`; the first lines give the group, α and μ.
  The best S so far is always in OUT.txt.best.
- Env vars: ORBIT="k m f" (k odd prime: 3 or 5; f = 1; 1 + k m = 16), TARGP (% targeted candidates, 70),
  TMAX (1.5), TMIN (0.15), COOLSTEPS (4), REHEATSTEPS (60), AT (choice of g), AR (choice of r).
  `EVAL=file UNCPRINT=1 $HB 16 10 0 1 1 /dev/null FAMILY P N` prints the cost of a solution file and its holes
  (use slot.sh for it too: it is a full evaluation, ~10 s).
- Groups: `python3 $R/groups.py 2.30e9 2.32e9 5` lists every SL/PSL(2,p) × Z_n in the band that supports k = 5
  (every prime factor of n is 1 mod 5), with μ, fixed-set size and predicted holes (use 3 for k = 3).
- How to wait for a background run without a foreground sleep:
  `timeout 590 bash -c 'until grep -q "^RESULT" run.out 2>/dev/null; do sleep 20; done'` (repeat if needed).
  Start the run itself with `nohup ... &` so your Bash call returns.

## Score

The scoreboard score is the **best cost at the end of your run** (lower is better; 0 = solved). Also report μ, the
number of evals, and the step (evals) at which the best was first reached, and how many of the final holes are
α-fixed (z = 0 and commuting with g; `EVAL ... UNCPRINT=1` lists them; the log's "alpha: conj by mat(...)" line
gives g).

## Machine rules

- THREADS=1; every heavy run through `$R/slot.sh cN timeout ... nice -n 10 ...`; at most 2 heavy runs per card,
  one at a time; no other heavy computation. Python one-liners are fine.
- No git commands. Write only inside your folder `$R/cN/` plus your one scoreboard line.
- Your whole card: at most ~60 minutes wall clock including waiting for a slot.

## Output

Append ONE line of valid JSON to `$R/scoreboard.jsonl` with python3:

    {"card": "cN", "idea": "<one line>", "code": "<path of your log>", "command": "<exact command>",
     "score": <best cost>, "valid": true|false, "mu": <μ>, "evals": <n>, "fixed_holes": <n>,
     "next": "<one line: what you would try next>", "data": "<short raw numbers>"}

"valid" = your run reached cost 0. Then reply to Opus in at most 5 lines.
