# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 14:20 UTC, job cell-11-5 (session_014q81WuY3QXemLJTaF8MiA2), goal (11,5) > 7,020, round r1-d11D5

Context: the cell was taken at 7,020 (W(8) + doubled matching over Z6, DM_D5.md) while this job was paused, so the
goal moved to > 7,020. Cards (scoreboard: r1-d11D5/scoreboard.jsonl):
- c1 algebraic Z3 cocycles on W(7) (cubic character of polynomial flag functions), for the tripled matching over Z9 (7,200): best 15,503, random level ≈ 16,000. Nothing.
- c2 group-invariant Z3 cocycles on W(7): no report at the time of writing.
- c3 σ-exemptions plus joint annealing of σ and ν on W(7): no report at the time of writing.
- c4 mixed chart lift over F3 (3 letters + 2 unit colours): valid only up to 2,916 (m = 18). At 7,128, 3.8% of pairs are far.
- c5 mixed chart lift over F4 (2 letters + 3 units) and F2: no diameter-5 lift at any m tried; 204k far pairs at 7,168.
- c6 Z4 lifts of the 1,782-vertex (11,4) graph: no report at the time of writing.
- c7 other W(q) + parallel-jump bases: exact walk-count bounds rule out W(5)+5/Z23, W(4)+6/Z42, W(3)+7/Z88. W(7)+2+1 over Z9 annealed to 82k far pairs (weak annealer).
- c8 augmentation of the 7,020 graph: every one of its 38,610 edges is critical (each deletion creates a distance-6 pair), and 20,000 twin-vertex attachments all failed.
Kept: nothing from the cards directly. c8's "every edge critical" pointed Opus to non-GQ bases for the
doubled-matching lift: W(8) plus one extra point-line pair (586 + 586), which would give 7,032 (see research/d11D5/NOTES.md).
