# beyond-d13b squad cards: rules common to every card

Job beyond-d13b (2026-11-01/02, Opus director). Goal: raise the D = 13 column at Δ = 5..10 of
research/frontier/beyond/BEYOND_TABLE.md. Each card runs in its **own cloud container** (4 cores, 15 GB, a fresh clone
of branch claude/beyond-d13-extend-5n8uwl). The container is deleted when you send your final reply, so **only your
final reply is kept**.

## Rules

1. Work from the repo root. First run `bash research/squads/beyond13b/tools/setup.sh` (builds the tools into
   research/frontier/beyond13/bin, ~30 s). Work in a folder `work/` at the repo root (`mkdir -p work && cd work`);
   binaries are then `../research/frontier/beyond13/bin/<name>`.
2. **Every Bash command must finish in under 110 s.** Start every search with
   `bash ../research/squads/beyond13b/tools/bg.sh TAG <command>` (it returns at once; env vars before `bash` pass
   through), then call `bash ../research/squads/beyond13b/tools/poll.sh TAG [TAG...]` again and again (each call waits up
   to 95 s and prints RUNNING/FINISHED, minutes, the last log lines). Never use `sleep` as a command of its own.
3. **Never end your turn while a run is going.** Your container dies with your reply and kills the run. Keep polling
   until your runs finish or your time box is used up, then kill leftovers (`pkill -f bin/`) and reply.
4. Use all 4 cores and at most 12 GB memory in total (haar_big0 needs N/2 bytes; at N = 1.5e10 that is 7.5 GB, so one
   run at a time there).
5. No git commits or pushes; do not call any MCP, session, remote or scheduling tool; do not contact anyone.
6. Write plainly. A "valid" claim needs cost 0 from the search program itself (it re-evaluates its best S at the end:
   `re-evaluation of the best S: cost 0`), and where the card says so, an independent checker run.

## Final reply (the only thing kept), in this order

1. One JSON line: `{"card": "<id>", "cell": "(d,13)", "idea": "<one line>", "command": "<exact command of the best
   run>", "score": <vertices 2N of the best cost-0 graph, or 0>, "best_cost": <lowest cost at the largest group tried>,
   "valid": true|false, "next": "<one line>"}`
2. For every cost-0 solution: the RESULT line and the solution file **verbatim** (`cat` it: a header line plus one line
   per generator). For f = 0 runs (ORBIT "3 m 0") also the `.orb` file.
3. For your best non-zero state at the largest group: the cost and the `.best` file verbatim (it is short).
4. At most 5 lines of notes: what you learned (stalls, which groups looked easy or hopeless, evaluation speed).

## Tools (all in research/frontier/beyond13/bin after setup)

- `haar_big0 d D seconds seed K outfile sl|psl p n` with env `ORBIT="k m f"` (S = e + (f-1) random alpha-fixed
  generators + m alpha-orbits of size k = 3; f = 0: m free orbits, no e), `THREADS`, `START=<file.best>` (continue from
  a state; for f = 0 use the `.best.orb` file), `TMAX` (1.5), `TMIN` (0.15), `COOLSTEPS` (4), `REHEATSTEPS` (60),
  `TARGP` (70), `EVAL=<file>` (print the cost of a solution and exit), `RANDORB=m` (cost statistics of m random
  symmetric S). Prints `t=.. step=.. evals=.. cost=.. best=..` lines and a final `RESULT ... best=C ...` line; stops at
  cost 0 and writes outfile; writes outfile.best after every improvement. Group G = SL(2,p) x Z_n or PSL(2,p) x Z_n.
- `hmeta d D seconds seed K outfile m k r` (Z_m x|_r Z_k, random S), env `THREADS`, `T0` (2), `T1` (0.2),
  `REHEAT` (40), `START=<file.best>`, `EVAL=<file>`. Odd-order Frobenius groups: `python3
  ../research/frontier/beyond13/meta/mpick.py d D Nlo Nhi [k1,k2,..]` lists "m k r N mu".
- `haar_gen3 d D seconds seed K outfile GROUP... n` (random S; GROUP = meta m k r | sl q | psl q | prod GROUP GROUP),
  env THREADS, COOL, REHEAT. `haar_gen3s` adds `SAVEBEST=<file>` / `START=<file>`; `haar_gen3t` adds `TFULL=1`
  (full-length targeted moves).
- Checkers: `haarcheck_gen SOL` (SL/PSL x Z_n; env OMP_NUM_THREADS=4), `python3
  ../research/frontier/beyond13/metacheck.py SOL` (metacyclic), `metacheck2.py SOL` (products of metacyclic groups).
- `python3 ../research/squads/beyond13b/tools/cands.py d 13 lo hi [sl|psl|both] [pmax] [nmax]`: SL/PSL x Z_n with
  lo <= 2N <= hi, with mu = N exp(-W/N) (size law) and "special" = expected odd-D special holes (central elements,
  PSL involutions; research/frontier/beyond11/ODD_D_HOLES.md).

## Background (read only if you need it)

research/frontier/beyond/BEYOND_TABLE.md (section "D = 13 at Δ = 3..10"), research/frontier/beyond13/THEORY.md,
research/frontier/beyond11/ODD_D_HOLES.md, research/frontier/beyond11/FROBENIUS.md, research/structured/STRUCTURE.md.
Key facts: at odd D the hard elements are involutions and central elements, so SL(2,p) x Z_n with small odd n beats
PSL (PSL with n = 1 is the worst shape); orbits of size k = 3 (k = 2 is bad); f = 0 when 3 | Δ. Orbit search needs about
e^(mu/4.5) evaluations; random S about e^(mu/2). At Δ = 4, 5 odd-order Frobenius groups Z_p x|_r Z_k (k odd, 13..63)
with random S do best.
