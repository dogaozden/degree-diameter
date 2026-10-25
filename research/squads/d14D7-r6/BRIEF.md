# Squad round d14D7-r6 (job cell-14-7): mirrored extensions of the 756 set

## Background (read research/cell147/mirror/README.md first, 5 minutes)
The (14,7) graph is 5 copies of the hexagon H(11) with a "surgery set" R' of points: n = 1,771,560 + 4|R'|.
Master: |R'| = 756 (a pairwise-opposite set, research/d13D7/sets/R756_r4c1_idx.txt). New rule (proved and checked):
R' may contain distance-4 pairs if the line side mirrors them exactly. Concretely we add extra points X to R756 and one
line per extra point, and we need a bijection f from R756 (minus dropped points) into the Hermitian spread S (1,332
pairwise-opposite lines) such that for every extra pair (x_j, L_j): f(r) is at distance 4 from L_j exactly when r is at
distance 4 from x_j. This is a per-TYPE count condition: type(r) = {j : d(r, x_j) = 4}, type(s) = {j : d(s, L_j) = 4}
for a spread line s (spread lines concurrent with some L_j are unusable). Base points whose type has too few spread
lines are DROPPED (cost 1 each). Score F = (number of extra points k) - (number dropped); |R'| = 756 + F.
Constraints: X pairwise opposite (B(x, y) != 0), every x non-collinear with R756 (76,608 candidates); the lines
pairwise opposite and not in S. Current best: F = 11 (k = 11, nothing dropped), |R'| = 767, (14,7) 1,774,628.

Why it is hard: a random line L is at distance 4 from 121 spread lines and concurrent with 1; a candidate x is at
distance 4 from 60-78 base points. With many pairs, base points get rare types (sets of 3+ pairs) that no spread line
has. Annealing (research/cell147/mirror/mirror_sa4.py) stalls at F = 11. Points have LINEAR structure (the 12 points of
a projective line partition R756 by orthogonality), lines do not (for a line M and a spread line s opposite M, each
point of M has exactly one line through it at distance 4 from s).

## Tools (python3, numpy; all in research/cell147/mirror/)
- hexmod.py: class Hex (H(11) incidence: lp = points of each line, pl = lines through each point, X = coordinates,
  Bmat(I, J) bilinear form matrix (0 = orthogonal), line_ball(l) = (lines at distance 2, lines at distance 4),
  collinear_points(p), lines_meeting(l)). Hexagon file: /tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/hex_q11.bin
  R756 indices: same folder R756idx.npy; Hermitian spread lines: S_herm.npy.
- mirror_sa4.py SEED OUTDIR [--init STATE.npz] [--secs S] [--T 0.15]: baseline annealer; writes OUTDIR/best.npz.
- inspect_state.py STATE.npz: type statistics (which types are tight).
- mirror_build.py STATE.npz SEED OUTDIR: THE SCORER. Re-checks everything (non-collinear, opposite where needed, exact
  mirroring of every distance-4 pair), drops base points whose type is short, prints
  "|R'| = N (dropped d of the base set, added k)". A state file is an .npz with arrays X (point ids), L (line ids),
  R (base ids = R756idx). Start from research/cell147/mirror/configs/state_k11_sa4.npz (F = 11) or from scratch.

## Scorer
`python3 research/cell147/mirror/mirror_build.py YOUR_STATE.npz 1 /tmp/...yourdir` -> your score is N - 756 (= F).
Only a state that mirror_build.py accepts counts.

## Rules (shared machine: 4 cores, Opus is running a 3-thread graph check)
- ONE process at a time per card, single thread, `timeout 900 nice -n 15 ...`; <= 1.5 GB memory.
- Work only in research/squads/d14D7-r6/<card>/ (scratch outputs may go to /tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/r6_<card>/). No git.
- Time box about 40 minutes.
- At the end append ONE JSON line to research/squads/d14D7-r6/scoreboard.jsonl:
  {"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command>", "score": F, "valid": true|false,
   "file": "<best state .npz path>", "next": "<one line>"}  and reply in at most 5 lines.
