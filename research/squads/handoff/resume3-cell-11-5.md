# Handoff: job resume3-cell-11-5 (round 3 of cell-11-5), Oct 25 2026

Session session_018TRrddhVEdN311drmbPpBK, branch claude/cell-11-5-bipartite-search-lyemfs (continues the round-2
branch; draft PR #388).

## Results
- **(11,5) ≥ 7,032** (was 7,020): DM Z6 lift of W(8) plus one point-line pair. research/d11D5/graphs/d11D5_n7032_CHECK.md
  (apsp.c VALID, diameter exactly 5, 11-regular, bipartite, 38,676 edges, sha256 4355f145...). Needs the coordinator's check.
- **(10,5) ≥ 4,812** (was 4,800, side result): W(7) plus one pair, research/d11D5/graphs/d10D5_n4812_CHECK.md.
- **(12,5) ≥ 9,852** (was 9,840, side result): W(9) plus one pair, research/d11D5/graphs/d12D5_n9852_CHECK.md.

## How (the pipeline that works)
1. Base with n > 585: W(8) + a point-line switch (research/d11D5/inc/mkinc.py, addpair.py, w8r/genk.py).
2. Structural cost (research/d11D5/plus/plusopt7.c, exact, 4 ms) to <= ~20 by po7 annealing (T0 20 -> 0.4), then to 0
   with the clause-weighting search wpo (research/squads/r3-d11D5/c2/wpo.c). wpo is strong from low cost and drifts
   upward from cost in the hundreds. Annealing, tabu, LNS, tempering and exhaustive 2-moves all stop at 2 at n = 586.
3. Flag cocycle nu: research/d11D5/inc/nujoint.c annealing, then SIGFIX=1 FIRST=1 (greedy sigma swaps that give a
   violated pair a sigma route), then TARGET=1 annealing (those swaps as moves, PS = 0.02). From 2 violated pairs
   TARGET reached 0 in 670 moves; plain annealing stalls at 5-30.
4. Check: research/d11D5/inc/finish.sh (z6lift exact lift cost, edge list, apsp.c).

## Open (in order)
1. **n = 587 (7,044).** Best structural cost 148 (research/d11D5/inc/inc2/n587_best148.in, a pair added to the 7,032
   base). Annealing plateaus at 150-230 whatever the start (8- or 9-flag switch, incremental or two pairs at once,
   T0 3-20, 91 points near the first pair frozen), and wpo drifts up from there. A single pair into W(8) reaches 10
   then 0 with the same tools, so the two pairs interfere through sigma. Ideas not tried: wpo with weights only on the
   triples of the newest pair; a lazy SAT/CP model for sigma with the base fixed (each coset +-1 triple (s, v) is one
   clause over the values of sigma(s) (route a) and of sigma on the points collinear with s (route b)); a design that
   places the second pair inside the first pair's covering structures.
2. **(10,5) ≥ 4,812 done** (side result, research/d11D5/graphs/d10D5_n4812_CHECK.md, apsp VALID): W(7) + one pair by
   inc/pipeline.sh in about 10 minutes. Needs the coordinator's check. (The first W(7)+1 base, from squad r3 c4, stays
   at one violated parity pair: every sigma swap that would cover it breaks the structure.)
3. **The same recipe at (14,5)**: W(11) + one pair gives 17,580 > 17,568. Base with the DM sigma and nu:
   research/d11D5/inc/wq/w11_dm.in/.nu; the run of this session is research/d11D5/inc/wq/run/W11.* (see its .out for
   where it stopped). Command: `SEED=111 SASECS=900 ./pipeline.sh wq/run/w11p1.in wq/run/w11p1.nu wq/run/W11 14 5`
   from research/d11D5/inc after `python3 addpair.py wq/w11_dm.in wq/w11_dm.nu b 1 wq/run/w11p1.in wq/run/w11p1.nu 1464`.
   Evaluations cost 10 ms at this size, so give the annealer 2,000+ CPU s. W(9) and W(7) + one pair are done.
4. The counting ceiling of the family is 14,796 at (11,5) (n <= 1,233), so the room is large; what is missing is a
   structural search that handles several new pairs at once.
