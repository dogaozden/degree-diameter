# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 19:05 UTC, cell-11-10 (Opus, cloud session), round 1: (11,10) above the table

Goal: (Δ, D) = (11, 10). The live wiki table (read over plain HTTP; HTTPS fails certificate checks here) has
130,592,354 (Eyal Loz). Opus before the round: haar_sym (research/structured, copied from branch
claude/structured-search-orbit-04hefm @ 03050f1) with ORBIT="3 3 2" solved SL(2,79) × Z133 (131,127,360) in 9
evaluations and PSL(2,149) × Z43 (142,235,400, μ = 11.7) in 89. At the table μ is only 2.7 (W = 1,111,111,111), so
the cell was open only because our copy of the table could not read it. Calibration: k = 3 0.09 s per evaluation,
k = 5 0.25 s, 1.3–1.4 GB per run at N ≈ 75M. The machine fits 4 heavy runs, so every heavy command went through a CPU-slot
gate (research/squads/d11D10-r1/gate.sh). Squad A = 8 search cards (15 slot-min each), squad B = 8 tool and analysis
cards (0–10 slot-min). Files: research/squads/d11D10-r1/{PREAMBLE.md, CARDS.md, scoreboard.jsonl}.

Cards: A1 k = 5 PSL small p, large n · A2 k = 5 PSL medium p · A3 k = 5 SL · A4 k = 3 PSL on A1/A2's groups ·
A5 k = 3 SL on A3's groups · A6 α pairings (AR/ALPHA) · A7 Frobenius α on SL(2,32) × Z_n · A8 search wildcard ·
B1 second PSL checker · B2 prime-power checker · B3 PGL checker · B4 ball-growth census · B5 speed knobs ·
B6 better orbit moves · B7 theory/plan · B8 open wildcard.
