# beyond-d13b squad cards: rules common to every card

Job beyond-d13b (2026-11-01/02, Opus director). Goal: raise the D = 13 column at Δ = 5..10 of
research/frontier/beyond/BEYOND_TABLE.md. All cards and the director share ONE machine (4 cores, 15 GB) and one repo
checkout at /home/user/degree-diameter. The director is running a 10 GB, 4-thread check of a 29-billion-vertex graph
there, so every card gets a slice of a core: about 0.1-0.25 core (round 2: less while the director's checks run). Be
frugal.

(A first launch on 2026-11-01 at 22:56 UTC told cards they had their own containers. They did not: 17 cards shared one
work/ folder, collided on file names, ran ~40 threads and got the director's check OOM-killed. These rules fix that.)

## Rules

1. **Your folder**: `research/squads/beyond13b/<round>/<card>/` (create it; `cd` there for every command). Never write
   outside it, except one appended line to `research/squads/beyond13b/<round>/scoreboard.jsonl` at the end.
2. **No git commands at all** (no fetch, reset, checkout, commit). Do not rebuild the tools: they are prebuilt in
   `/home/user/degree-diameter/research/frontier/beyond13/bin/` (call it `$B` below; write the full path).
3. **One run at a time, one thread, nice 10**: start every search with
   `bash /home/user/degree-diameter/research/squads/beyond13b/tools/bg.sh TAG <command>` (it forces THREADS=1 and nice 10
   and refuses while your previous run is alive). Then call
   `bash /home/user/degree-diameter/research/squads/beyond13b/tools/poll.sh TAG` repeatedly (each call waits up to 95 s and
   prints RUNNING/FINISHED, minutes, the last log lines). Short commands (a check of a small graph, python helpers) may run
   directly, under `timeout 100 nice -n 10`.
4. **Every Bash command must finish in under 110 s.** Never use `sleep` as a command of its own.
5. **Never end your turn while your run is going.** Keep polling until it finishes or your time box is used up; then kill
   it (`kill $(cat out/TAG.pid)`) and finish. Never touch processes you did not start.
6. Memory: at most 0.7 GB per run.
7. **Never call any tool whose name starts with `mcp__`** (interrupt_session, archive_session, read_documentation, ...):
   they act on the director's cloud session, not on your runs, and could end the whole job. Round-1 cards made several
   such calls with made-up ids (all rejected). To stop a run use `kill $(cat out/TAG.pid)`. Do not contact anyone.
   Write plainly.
8. A "valid" claim needs cost 0 from the search program itself (it re-evaluates its best S: `re-evaluation of the best
   S: cost 0`), plus the independent checker where the card says so. The director re-checks everything.

## At the end

1. Append ONE JSON line to `research/squads/beyond13b/<round>/scoreboard.jsonl`:
   `{"card": "<id>", "cell": "(d,13)", "idea": "<one line>", "command": "<exact command of the best run>", "score":
   <vertices 2N of the best cost-0 graph, or 0>, "best_cost": <lowest cost reached at the largest group tried>,
   "sol": "<path of the best cost-0 solution file, or of the best .best state>", "valid": true|false, "next": "<one line>"}`
2. Reply in at most 5 lines: best score, best near miss (group, cost), one thing learned.

## Tools ($B = /home/user/degree-diameter/research/frontier/beyond13/bin)

- `$B/haar_big0 d D seconds seed K outfile sl|psl p n` with env `ORBIT="k m f"` (S = e + (f-1) random alpha-fixed
  generators + m alpha-orbits of size k = 3; f = 0: m free orbits, no e), `START=<file.best>` (continue from a state; for
  f = 0 use the `.best.orb` file), `TMAX` (1.5), `TMIN` (0.15), `COOLSTEPS` (4), `REHEATSTEPS` (60), `TARGP` (70),
  `EVAL=<file>`, `RANDORB=m` (cost statistics of m random symmetric S, no search). Prints `t=.. step=.. evals=.. cost=..
  best=..` lines and a final `RESULT ... best=C ...` line; stops at cost 0 and writes outfile (+ `.orb` for f = 0); writes
  outfile.best after every improvement. G = SL(2,p) x Z_n or PSL(2,p) x Z_n.
- `$B/hmeta d D seconds seed K outfile m k r` (Z_m x|_r Z_k, random S), env `T0` (2), `T1` (0.2), `REHEAT` (40),
  `START=<file.best>`, `EVAL=<file>`. Odd-order Frobenius groups: `python3
  /home/user/degree-diameter/research/frontier/beyond13/meta/mpick.py d D Nlo Nhi [k1,k2,..]` lists "m k r N mu" (at most 3
  per k; narrow the range to get more).
- `$B/haar_gen3 d D seconds seed K outfile GROUP... n` (random S; GROUP = meta m k r | sl q | psl q | prod GROUP GROUP),
  env COOL, REHEAT. `$B/haar_gen3s` adds `SAVEBEST=<file>` / `START=<file>`; `$B/haar_gen3t` adds `TFULL=1`.
- Checkers: `$B/haarcheck_gen SOL` (SL/PSL x Z_n), `python3 /home/user/degree-diameter/research/frontier/beyond13/metacheck.py
  SOL` (metacyclic), `.../metacheck2.py SOL` (products of metacyclic groups).
- `python3 /home/user/degree-diameter/research/squads/beyond13b/tools/cands.py d 13 lo hi [sl|psl|both] [pmax] [nmax]`:
  SL/PSL x Z_n with lo <= 2N <= hi, with mu = N exp(-W/N) (size law) and "special" = expected odd-D special holes.

## Background (read only if you need it)

research/frontier/beyond/BEYOND_TABLE.md (section "D = 13 at Δ = 3..10"), research/frontier/beyond13/THEORY.md,
research/frontier/beyond11/ODD_D_HOLES.md, research/frontier/beyond11/FROBENIUS.md, research/structured/STRUCTURE.md.
Key facts: at odd D the hard elements are involutions and central elements, so SL(2,p) x Z_n with small odd n beats PSL
(PSL with n = 1 is the worst shape); orbits of size k = 3 (k = 2 is bad); f = 0 when 3 | Δ. Orbit search needs about
e^(mu/4.5) evaluations; random S about e^(mu/2). At Δ = 4, 5 odd-order Frobenius groups Z_p x|_r Z_k (k odd, 13..63) with
random S do best.
