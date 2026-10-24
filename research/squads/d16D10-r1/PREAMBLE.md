# Squad d16D10-r1: shared preamble (read this first)

Job "cell-16-10" (Opus researcher, cloud session, 2026-10-24). Goal of the whole job: a bipartite graph of maximum degree
16 and diameter 10 with more than 4,119,507,330 vertices (the 2013 table value). We will do it with a Haar graph
H(G, S), |S| = 16: vertices (g,A), (g,B), edges (g,A) ~ (s g, B). It has 2|G| vertices, so we need |G| > 2,059,753,665.

The main line (Opus): G = SL(2,p) × Z_n with |G| ≈ 2.1–2.25 billion and an orbit-symmetric S, ORBIT="3 5 1"
(S = {e} ∪ 5 orbits {x, αx, α²x} of an automorphism α of order 3; research/structured/STRUCTURE.md §1–§3 explains why
this beats random S). Opus is writing a new low-memory evaluator for that size. One evaluation there costs ~1–2 s, so
the expensive run can afford only ~10³–10⁴ evaluations in total. **Your card answers one question at a cheap proxy
scale (~10 ms per evaluation), so Opus can pick the structure, group and parameters for the expensive run.**

## The proxy

(Δ, D) = (16, 8) with |G| ≈ 13–14 million. This is NOT a record attempt (the (16,8) table is far higher); it is a
measurement. Cost of S = number of B-side elements not within distance D−1 = 7 of (e,A); cost 0 = solved (diameter 8).
μ = N·e^(−W/N) is the expected cost of a random S (W = 183,063,616 binding words at (16,8)); μ grows fast with N:
N = 13.0M → μ 10, 13.5M → 17, 13.8M → 24, 14.0M → 29. Search effort grows roughly like e^(μ/4.5).

Reference measurement (Opus): `ORBIT="3 5 1" haar_sym 16 8 90 1 8 /dev/null sl 53 91` (N = 13,542,984, μ = 18.25)
solved, `RESULT ... best=0 evals=3017 time=37.9`.

## Tools (already built; do not rebuild, do not edit)

    T=/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured
    $T/haar_sym      structured search (README.md in $T has every env var; STRUCTURE.md the theory and negatives)
    $T/haar_fast     plain (non-symmetric) annealing, same CLI without ORBIT
    $T/tools/orb_screen.py  lists/screens groups:  python3 $T/tools/orb_screen.py 16 8 13000000 14200000 "3 5 1" --list

Usage: `ORBIT="k m f" [VAR=x ...] timeout 400 nice -n 10 $T/haar_sym d D seconds seed K outfile GROUP... n`
- d D = 16 8 for the proxy; seconds = wall-clock budget; seed = 1, 2, 3, ...; K = candidates per step (default
  recipe 8); outfile = /dev/null (or a file in your folder); GROUP = `sl p`, `psl p`, `pgl p`, `prod GROUP GROUP`, ...;
  n = the Z_n factor. The stdout line `RESULT d=16 D=8 group=... N=... best=<cost> evals=<n> time=<s> ...` is the
  measurement (best=0: solved; evals = cost evaluations used). Progress lines go to stderr.
- `RANDORB=m` instead of a search: cost statistics of m random symmetric S (a cheap screen; prints min/p1/p10/median).
- k must be odd (k = 2 creates word collisions, except in special cases), every prime factor of n must be ≡ 1 mod k,
  Δ = f + k·m.

## Score used by cards 1, 2, 3, 4, 6, 7, 8 (unless your card says otherwise)

E18 = (median over seeds of evals-to-solve) × exp((18 − μ)/4.5), with an unsolved run counted as 3 × its evals.
Lower is better; it normalises effort to μ = 18. Reference: sl 53 × Z91 seed 1 gives 3017 × exp((18 − 18.25)/4.5)
≈ 2850.

## Machine rules (shared: 4 cores, 15 GB; Opus's runs have priority)

- THREADS=1 (default); every run as `timeout <secs> nice -n 10 ...`; at most 2 runs at a time from your card;
  ≤ 1 GB memory per run; your whole card ≤ 20 minutes wall clock.
- No git commands. Write only inside your folder `research/squads/d16D10-r1/<card>/` (scripts, logs, notes) plus your
  one scoreboard line.

## Output

Append ONE line of valid JSON to `research/squads/d16D10-r1/scoreboard.jsonl` (use python3 to write it, e.g.
`python3 -c 'import json; open("research/squads/d16D10-r1/scoreboard.jsonl","a").write(json.dumps({...})+"\n")'`):

    {"card": "cN", "idea": "<one line>", "code": "<path of your script or log>", "command": "<exact best command>",
     "score": <number>, "valid": true|false, "next": "<one line: what you would try next>", "data": "<short raw numbers>"}

"valid" = your best run actually reached cost 0 (for the checker card: your checker agreed on every test).
Then reply to Opus in at most 5 lines.
