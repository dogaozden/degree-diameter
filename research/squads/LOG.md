# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-16-10 (Opus, cloud session_01LHP3CoLafNtH1CVkMxoTCW), round 1 (19:10–19:40 UTC): proxy calibration for (16,10)

Goal: beat the bipartite (16,10) table value 4,119,507,330 (DS14v2), i.e. a Haar graph on |G| > 2,059,753,665.
At the table order μ ≈ 4, so the cell is a compute problem: the existing tools need ~14 bytes per element (31 GB).
Opus wrote research/bighaar/haar_big.c meanwhile (rows = cosets of U × Z_n, N/2 bytes). Squad cards ran on a
cheap proxy, (16,8) at |G| ≈ 13.5M (μ ≈ 18), to choose structure, group shape and search parameters. Preamble and
cards: research/squads/d16D10-r1/PREAMBLE.md, CARDS.md; scoreboard research/squads/d16D10-r1/scoreboard.jsonl.
Score E18 = median evals-to-solve × exp((18 − μ)/4.5) (unsolved counted 3×); reference sl 53 × Z91: 2854.

Cards: c1 μ calibration · c2 group shape (n = 1 / small / medium / large) · c3 SL vs PSL vs PGL · c4 annealing
parameters · c5 a new independent checker · c6 other group families · c7 α / orbit variants · c8 wildcard.

Outcomes (the box ran at load 11–15 from 16 concurrent proxy jobs, so most wall-clock budgets were censored):
- c1: ln(evals) ≈ 0.84 + 0.36 μ at the proxy (solved μ 9.4, 13.9, 18.3; μ 21.9 not solved in 240 s).
- c2: small n looked best (sl 101 × Z13, μ 15.5: 3/3 solved, 25–433 evals); n = 1, 91, 199 censored. Not separated
  from μ.
- c4: K = 4 beat K = 8 (2/3 vs 0/3 solved in 60 s); noisy.
- c5: hcheck5.c, a new OpenMP checker from the definitions (2-bit level labels mod 3, BFS from both sides);
  8/8 agreement with haarcheck_sl on valid and corrupted files; ~18 min projected at N = 2.2e9 on 2 threads.
- c6: no family beat sl 53 × Z91 (PSL(2,49) × Z229 solved once at μ 16.8).
- c8: local move (orbit representative x → x·t or t·x, t a generator of another slot): E18 1234 vs 2854,
  2/3 seeds solved; promising, thin evidence.
- c3, c7: (pending at time of writing)
Kept: K = 4 for the expensive runs; hcheck5 as a second checker (Opus read the code: correct). Opus's own runs
then showed the proxy is much harder than the target: at (16,10) μ = 7.1 solved in 25 evaluations and μ = 15.3 in 21.

## 2026-10-25, cell-16-10 resume (Opus, cloud session_01NiptgUrtaeA398Fz5x8PkG), round 2 (12:51–13:45 UTC): the real target

Goal: (16,10) beyond our 4,386,127,200, at |G| 2.30–2.32e9 (μ ≈ 38–41, 4.60–4.64e9 vertices). Each card did one
600 s haar_big run (k = 5 unless noted) through a shared 2-slot pool (research/squads/d16D10-r2/slot.sh), so the cards'
runs queued behind each other; preamble, cards and scoreboard in research/squads/d16D10-r2/. Score = best cost.

Cards and best cost (holes: f = α-fixed, o = free orbits of 5):
- c1 tiny p, huge n, PSL(2,31) × Z154571 (μ 38.4): 355 and 375 (71 free orbits, 0 fixed). Nearly cyclic is hopeless.
- c2 SL(2,61) × Z10141 (μ 38.8): 12 (2 o + 2 f), at eval 177; a greedy continuation from it gained nothing in 254.
- c3 PSL(2,71) × Z12871 (μ 39.3), default schedule: 21 (4 o + 1 f), reached at eval 9.
- c4 PSL(2,191) × Z661 (μ 39.3): 19 (3 o + 4 f).
- c5 k = 3, PSL(2,61) × Z20287 (μ 38.9): 45.
- c6 PSL(2,71) × Z12871 with TMIN 0.5: 21 (4 o + 1 f); no better than c3's default.
- c7 PSL(2,71) × Z12871, three 200 s restarts: 25, 25, 31 (worse than one 600 s run).
- c8 wildcard k = 15 (m = 1) on PSL(2,31) × Z154591: 178,725 (the Z_n part of the 15-letter orbit is far too regular).
Nothing solved. What it told Opus (and matched the random-sample screen and Z_n-uniformity score the same hour): large n is
bad (c1, c5, c8), k = 5 beats k = 3, fixed holes are the large-p tax (c4: 4 of its 19), schedule changes and restarts
do not help (c6, c7). Opus meanwhile solved μ 30.9 and μ 35.7 on PSL(2,151) × Z1321 / Z1331 with the new FIXF screen
(4,547,938,800 and 4,582,366,800 vertices), and moved the main line to PSL(2,191) × Z661 with the screen (which removes
c4's 4 fixed holes). No round 3: the machine (4 cores, memory-bandwidth bound) is the limit now, and the remaining ideas
(k = 7 with a fixed generator, an orbit quotient of the BFS) are code, not cards.
