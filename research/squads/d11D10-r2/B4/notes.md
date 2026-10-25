# B4: checker readiness for psl 243 (final)

Started 12:49 UTC; wrapped up about 13:40 (past the 40-min box, because gate slots were queued for long stretches).
Heavy use: about 190 s of gated checker and haar_sym wall time (about 3.2 slot-min of the 6 budget). THREADS unset
(`env -u THREADS` on every gated run). No B4 process is running at the end.

## Small cases: PSL(2,243) x Z_1, |G| = 7,174,332, 2|G| = 14,348,664 vertices, Delta 16, D 8
Header of all four files: `16 8 psl 243 poly x^5+2x+1 n 1 N 7174332`.

| file | how made | haar_sym own check | haarcheck_pq | pqcheck |
|---|---|---|---|---|
| d16D8_psl_243_1_orb5_frob1_s1.txt | `ORBIT="5 3 1" AFROB=1 haar_sym 16 8 60 1 8 ... psl 243 1` | cost 0 at evals 1, "full diameter check: OK" | VALID eccA=8 eccB=8 (6.7 s, 11 MB) | VALID eccA=8 eccB=8 (12.3 s, 117 MB) |
| d16D8_psl_243_1_plain_s2.txt | `haar_sym 16 8 60 2 8 ... psl 243 1` (no ORBIT) | cost 0 at evals 1, "full diameter check: OK" | VALID eccA=8 eccB=8 (6.8 s) | VALID eccA=8 eccB=8 (12.2 s) |
| corrupt_repeat_from_s1.txt | valid #1, generator 7 replaced by a copy of generator 3 | none (see caveat) | INVALID "generators not distinct" | INVALID "repeated generator 3 7" |
| corrupt_breakdet_from_s2.txt | valid #2, one entry of generator 5 changed, det != 1 | none (see caveat) | INVALID "matrix not in SL (det != 1)" | INVALID "determinant != 1: 5 mat(93,242,53,25) z=0" |

Verdict: both checkers agree on all four files. The two valid files get identical eccentricities from both; the two corrupted
files are rejected by both, each at the parsing stage.

Caveats:
- The "changed generator" copy breaks det = 1, so it tests parsing only, not the diameter path. A det-preserving change
  of one generator in a loose graph would probably stay VALID; not run.
- haar_sym has no check-only mode (CKPT resume only accepts alpha-invariant S), so there is no haar_sym verdict on the
  corrupted copies. The haar_sym agreement is only its generation-time "full diameter check: OK" on the two valid files.

## Big file timing: 157,835,304 vertices (PSL(2,243) x Z_11, D = 10, 11 random generators, N = 78,917,652)
This file is INVALID (diameter 11 > 10); it was built only for timing.

| checker | wall | BFS from (e,A) / (e,B) | user | peak RSS | result |
|---|---|---|---|---|---|
| haarcheck_pq | 85.6 s | 48.2 s / 37.4 s | 70.8 s | 40 MB | INVALID, eccA = eccB = 11, unreached 0 |
| pqcheck | 62.3 s | 31.0 s / 31.3 s | 58.4 s | 168 MB | INVALID, eccA = eccB = 11 |

Both ran to completion (the 100 s cap was not reached). The machine was loaded (load average 5 to 6 on 4 cores from other
gated jobs), so these wall times are indicative. The checkers agree on the verdict and on the eccentricities.
Opus's solution check logs (opus/check_pq_s201.log and opus/check_pqcheck_s201.log, read by me) both report VALID with
eccA = eccB = 10 for the 157,835,304-vertex s201 solution, as the coordinator said. I did not run that file myself.

## Open points
- pqcheck's eccentricity is one too large when the BFS does not reach everything (read from the source; the final empty level
  is counted). Verdicts are unaffected. Not exercised here.
- wait_then_chain.sh and chain_big.sh were not used for results (the first was killed by mistake before it ran).

## Files (all in this folder)
- Valid: d16D8_psl_243_1_orb5_frob1_s1.txt, d16D8_psl_243_1_plain_s2.txt
- Corrupted: corrupt_repeat_from_s1.txt, corrupt_breakdet_from_s2.txt
- Big timing file (INVALID): big_psl_243_11_r11_s1.txt
- Tools: mkcases.py (GF(243) arithmetic, file builder), runtimed.py (wall time, peak RSS, timestamped output),
  chainA.sh / chainB.sh / chain_small.sh (checks run through the gate), logs/ (every run log; RUNTIMED line = timing)
- haar_sym (research/structured/haar_sym) and the checkers (research/squads/d11D10-r2/tools) were not modified.
