# Squad round r3-d11D5 (job resume3-cell-11-5, Oct 25 2026): structural cost 0 for a DM base with n > 585

Goal: (11,5) > 7,020. The record is the Z6 doubled-matching (DM) lift of W(8): base = incidence graph of W(8) (585 points,
585 lines, 9-regular) + a point->line bijection sigma whose edges are doubled; the lift has 12n vertices. A base with
n = 586 (W(8) + one extra point x* and line l*) gives 7,032, n = 587 gives 7,044, ... Background: research/d11D5/NOTES.md,
section "The open lead". Round r2 (research/squads/r2-d11D5/scoreboard.jsonl) and the previous Opus got the exact
STRUCTURAL cost of an n = 586 base down to 2 (one failing pair) but never to 0. Your job: a base (any n > 585, dg = 9)
with structural cost 0. (Opus then solves the flag cocycle and checks the lift.)

## File format (".in")
    n dg
    n lines: the dg point ids (0..n-1) of line l, for l = 0..n-1
    n lines: sigma(p) (a line id) for p = 0..n-1      (a bijection)

## Scorer (exact, about 4 ms)
    gcc -O3 -march=native -o po7 /home/user/degree-diameter/research/d11D5/plus/plusopt7.c -lm   (compile in YOUR folder)
    SCORE=1 ./po7 file.in        -> "n=586 dg=9 cost=C hot points=H"; C = 0 is the target.
Cost = number of (source, target, coset) triples that fail: cosets 1, 2 need a walk of length <= 5 in the Z3 quotient
(jump point->line = +1, line->point = -1) with the right parity; coset 0 needs pure distance <= 2 (same side) / <= 3
(opposite side), or a walk with >= 1 jump and jump sum 0 mod 3, or >= 2 pure walks of length 4 (same side) / 5 (opposite).
Annealer built in: `SECS=600 SEED=1 T0=20 T1=0.5 PF=0.3 PH=0.7 OUT=best.in OUT0=fail0.in ./po7 start.in` (sigma swaps
with prob 1-PF, degree-preserving flag swaps (p1,l1),(p2,l2)->(p1,l2),(p2,l1) with prob PF, PH = prob of picking a
hot vertex; it writes OUT0 and stops when it reaches cost 0). Read plusopt7.c to reuse its total() in your own code.
Failure classifier: `python3 /home/user/degree-diameter/research/d11D5/inc/anal.py file.in 10` (prints failure types
(coset, side pair, pure distance, number of pure walks) and examples (source, target); ids >= n are lines n + l).

## Data and generators
- research/d11D5/w8.json (points as PG(3,8) coordinates, lines), `from dcover import load; n, L, d_pt, d_ln, inv = load(8)`
  (run from research/d11D5): L = lines (lists of point ids), d_pt[p] = delta(p) a line, d_ln[l] = delta(l) a point
  (delta = the polarity of W(8); point p lies on line delta(R) iff R lies on delta(p)).
- research/d11D5/plus/mkplus.py: 9-flag switch (x* on 9 old lines L_i, l* through their old points p_i).
- research/d11D5/plus/mkreg.py + hline.py (hline.py writes plus/hcand.json: hyperbolic PG-lines h, delta-images, transversals).
- research/d11D5/inc/mkinc.py: the 8-flag "incident" switch (x* on l*, x* on 8 old lines L_i, l* through 8 old points p_i
  and x*). K=8 env; modes spread | random | absolute. Starts score about 1,700-2,450.
- Best cost-2 states of r2: research/d11D5/plus/best_y901.in, best_f5.in, best_g61.in, best_u602.in (n = 586).

## Machine rules (4 cores, 15 GB shared by 9 workers)
ONE heavy process at a time per card, always `timeout 900 nice -n 10 <cmd>`, THREADS=1, < 1.5 GB memory. No git commits.
Write only inside your card folder research/squads/r3-d11D5/<card>/. Total wall time about 45 minutes, then report.

## Scoreboard
Append ONE json line to research/squads/r3-d11D5/scoreboard.jsonl:
{"card": "c5", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <lowest structural cost>,
 "valid": <true iff cost 0>, "best_file": "<path of the best .in>", "next": "<one line>"}
and reply in at most 5 lines. If you reach cost 0, save the file in your folder and say so on the first line.
