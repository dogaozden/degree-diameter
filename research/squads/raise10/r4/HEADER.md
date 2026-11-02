# Squad raise10, round 4: shared rules (read this first, then your card)

Job raise-d10 (Opus director, 2026-11-01/02, branch claude/raise-d10-beyond-rcdq5p). Goal of the job: raise our
diameter-10 values of the bipartite degree-diameter problem at Δ = 3..20. You are one Haiku card. Your card names ONE
cell (Δ, 10) and ONE strategy. A find counts only if it beats the current value of that cell (table below) and passes
the checker named in your card.

Current D = 10 values (vertices = 2N for a Haar graph of a group of order N):

| Δ | value | how | Δ | value | how |
|---|---:|---|---|---:|---|
| 3 | 810 | voltage lift of a 5+5 cubic base over C3 x He3 | 9 | 24,099,600 | PSL(2,151) x Z7, ORBIT "3 3 0" |
| 4 | 12,416 | Haar, meta Z97 x\|_19 Z64 (N 6,208) | 10 | 64,294,560 | PSL(2,81) x Z121, k = 5, f = 0 |
| 5 | 95,472 | Haar, meta Z1989 x\|_461 Z24 (N 47,736) | 11 | 157,835,304 | PSL(2,243) x Z11, orbit of size 10 |
| 6 | 524,160 | Haar, SL(2,5) x PSL(2,7) x Z13, "3 2 0" | 12 | 332,797,296 | SL(2,157) x Z43, "3 4 0" |
| 7 | 2,298,240 | Haar, SL(2,7) x PSL(2,19), k = 3 | 13 | 683,943,456 | SL(2,137) x Z133, "3 4 1" |
| 8 | 8,043,840 | Haar, PSL(2,7) x PSL(2,19) x Z7, k = 3 | 14 | 1,350,537,864 | PSL(2,157) x Z349, "3 4 2" |

## New in round 4 (read)

- Rounds 1-3 (research/squads/raise10/r1..r3/, scoreboards there) found no raise of (3..8,10); 49 cards. Best states (cost =
  holes left; START-able solution files):
  - (5,10): Z1453 x|_11 Z33 **cost 1 with the Sidon constraint** (r3/g03/s1453_201.sol.best; tool r3/g03/hmeta_sidon.c with env
    SIDON=1; its exhaustive Sidon 1-opt has no solution); A4 x (Z239 x| Z17) cost 1 (r2/e07; a strict local minimum for 15 % of
    the 1-opt, rest unchecked); Z2857 x|_64 Z17 cost 2 (r3/g05); (Z7 x| Z3) x (Z137 x| Z17) cost 3 (r3/g02).
  - (6,10): Z6397 x|_5330 Z41 cost 1 (r2/e08; a strict 1-opt local minimum) and cost 3 in r3; Z5851 x| Z45 cost 3;
    (Z43 x| Z3) x (Z157 x| Z13) cost 3 (r3/g16/f105t.best).
  - (4,10): (Z7 x| Z3) x (Z43 x| Z7) (N 6,321) cost 3 (r3/g09/D_s4t.best). The director's exhaustive search (exh4) covers every
    Frobenius group and every Z_p x| Z_k with r of order k/2 in the window; none has a solution so far.
  - (3,10): non-abelian lift Z28 x| Z3 (order 84) on a 5+5 base cost 14 (r3/g12, tool r2/e13/nlift.c); Heawood x Z58 cost 6.
- Measured (r3/g14): median holes / size-law mu at (5,10): A4 x F and (Z7 x| Z3) x F ~1.5, Frobenius ~2; at (6,10)
  Z6397 x| Z41 1.3 (best family). Sidon (r3/g03): removes the catastrophic S (mean start cost 64 vs 2,080), median 48 vs 60.
  For d = 5 the Sidon condition needs k >= 21 (20 distinct nonzero differences), for d = 6 k >= 31.
- hmeta's candidate arrays hold K <= 64: never use K > 64 (r3/g04 found the overflow).
- Near the limit solves come from many fresh lineages; one cost-1 state rarely finishes.

## Machine rules (4 cores and 15 GB shared by up to 17 cards and the director's big searches)

- Every command you run: `timeout 110 nice -n 10 <cmd>` (hard limit 110 s per command; a longer command is moved to the
  background and you then sit idle). Long searches are CHAINS of 100-second links: save the best state, restart from it.
- THREADS=1 (or OMP_NUM_THREADS=1) always. One process at a time. Never `&`, `nohup` or background jobs.
- At most 1.5 GB of memory per process (haar_big0 prints its memory on the first line; haar_gen3/hmeta use ~20 bytes per
  group element).
- No git commands. Write only inside your card folder `research/squads/raise10/r4/<card>/` (create it), plus ONE line
  appended to `research/squads/raise10/r4/scoreboard.jsonl` at the end.
- Never kill a process you did not start (no `pkill -f`, no `killall`). Never call session, messaging, scheduling or
  GitHub tools (create_session, send_message, send_later, etc.): you have no reason to, and earlier cards that did caused
  trouble. Only Bash, Read, Write, Edit, Grep, Glob.
- **Use the whole time box: 25 minutes of wall time.** Earlier squads stopped after 6-12 minutes; do not. If your first
  plan dies early, try the next variant of the SAME strategy (other groups, other seeds, other bases) until 25 minutes.

## Tools (already built; do not rebuild unless a card says so)

Paths: work from the repo root /home/user/degree-diameter. `tools/` means research/squads/raise10/tools/.

Binaries in `research/squads/raise10/tools/bin/` (sources next to it in `tools/`):
- `haar_big0 d D seconds seed K outfile psl|sl p n` with env `ORBIT="k m f"`, `FIXF=1`, `BOUNDCUR=1`, `TMAX`, `TMIN`,
  `START=file`, `RANDORB=m`, `EVAL=file`, `THREADS=1`. Orbit-symmetric Haar search on PSL/SL(2,p) x Z_n (p prime):
  S = {e} + (f-1) alpha-fixed generators + m alpha-orbits of size k (d = f + k m); f = 0 means m free orbits, no e.
  FIXF=1 (needs f >= 1, D = 10 only) screens each candidate's holes among the alpha-fixed elements exactly (~0.1 s) and
  only evaluates candidates with none: it targets exactly the "last hole is an alpha-fixed element" plateau that stopped
  earlier sessions. Writes `outfile` on cost 0 and `outfile.best` after every improvement; `START=outfile.best` resumes
  (the fixed generators come from the file). Memory N/2 bytes. Full help: the comment at the top of
  research/frontier/raise10/haar_big0.c.
- `research/frontier/raise10/pick5.py d mu_lo mu_hi k pmin pmax psl,sl`: groups PSL/SL(2,p) x Z_n with an element of
  projective order k and every prime factor of n = 1 mod k, by size-law mu = N exp(-W/N). Pick mu so that 2N > value.
- `haar_gen3 d D seconds seed K outfile GROUP... n` (random S, any family: `meta m k r`, `sl q`, `psl q`, `pgl q`,
  `agl1 q`, `prod G1 G2`, ...). `haar_gen3s` = same plus `SAVEBEST=file` / `START=file` (chains). `haar_gen3t` = plus
  `TFULL=1 TARGP=100` (full-length targeted moves, the finisher that solved two cost-1 states on Nov 1).
- `hmeta d D seconds seed K outfile m k r` (bit-parallel metacyclic Haar search, random S; env T0, T1, REHEAT, START,
  EVAL). For groups Z_m x|_r Z_k (r^k = 1 mod m).
- `haar_sym` (orbit search, 32-bit, ~18 bytes/element), `haar_fast` (random S, fast): research/structured/README.md.
- `lift BASE n D seconds seed OUTPREFIX [T0 T1 L]` (cyclic voltage lifts of a bipartite cubic base; `liftd` = any degree
  with env DEG; `scan_h02` = exhaustive 1-opt + tabu finisher, same CLI, START=file). Bases in tools/bases/. Use
  L = 1200 for short runs (the default L = 20000 never cools in 100 s).
- `exh3 TABLE.bin D [OUTPREFIX]`: exhaustive cubic Haar graphs H(G,{e,x,y}) of a group table (tools/groups.py writes
  tables).
- Checkers: `python3 research/frontier/build_haar2.py SOL` (Haar, any family, up to ~2e7 vertices);
  `THREADS=1 tools/bin/hcheckpsl SOL` (PSL x Z_n, any size) / `THREADS=1 tools/bin/hcheck5 SOL` (SL x Z_n);
  `python3 tools/metacheck.py SOL` (metacyclic); `tools/bin/apsp EDGES` (all pairs, edge list "n" then "u v" lines; for
  graphs up to ~3e5 vertices); `tools/meta2edges.py` makes edge lists from metacyclic solutions.
- Notes worth reading for your strategy (skim, 2 minutes max): tools/FROBENIUS.md (Frobenius groups Z_p x| Z_k with
  random S won the small D = 11, 12 cells), tools/BEYOND13_README.md and BEYOND13_THEORY.md (lifts won Δ = 3 at D = 13, 14),
  research/structured/README.md and STRUCTURE.md (orbit search), research/frontier/SIZE_LAW.md.

## Scoreboard (one line of JSON, appended at the end; nothing else in that file)

`{"card": "c05", "cell": "9,10", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>",
"score": <vertices of your best VALID graph, or 0>, "best_cost": <lowest cost reached above the current value>,
"valid": true|false, "check": "<checker + log path>", "next": "<one line: what to try next>"}`

`score` is the vertex count of a graph that BEATS the current value and passed the checker; otherwise 0, and put your
closest attempt in `best_cost` (with its group in `idea`). Then reply to the director in at most 5 lines.
