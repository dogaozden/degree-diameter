# Squad round 5 preamble: climb the ladders with many short seeds

Tools, rules, report format: `/home/user/degree-diameter/research/squads/r1/PREAMBLE.md` and `r2/PREAMBLE.md` (Tools and
Machine rules sections). Files only under `/home/user/degree-diameter/research/squads/r5/<your card>/`. One heavy
process at a time, under `timeout <secs+100> nice -n 10`. About 50 minutes in total, then report. No git, no edits
elsewhere, nothing left running. To stop a process, kill it by PID (`pkill -f` can match your own shell).

## What worked in round 4 (four records)

- Small steps just above a record, with the record's own ORBIT structure.
- **Many short seeds beat a few long runs.** On A5 × SL(2,8) × Z37 at (7,10), ten 150 s seeds ended at 3, 1, 3, 1, **0**,
  1, 3, 3, 1; on SL(2,67) × Z13 at (8,10) a 900 s seed ended at 1 while another seed solved in 10 s. Solve times are
  heavy-tailed, so give each group several independent seeds.

## Protocol for each group in your list (in order)

1. Run seeds 1, 2, 3, … with the time per seed given on your card:
   `ORBIT="<k m f>" timeout <T+100> nice -n 10 $B/haar_sym d D T SEED 8 r5/<card>/<tag>_s<SEED>.txt GROUP n > r5/<card>/<tag>_s<SEED>.log 2>&1`
2. Stop the group as soon as one seed solves (`best=0`, `wrote ...`), or after the number of seeds on your card.
   If a seed ends at exactly 1 or 2 with ORBIT f ≥ 1, the leftovers are α-fixed elements: give the next seeds `ORBW=3`.
3. A solution: for 2N ≤ 3,000,000 vertices run `python3 /home/user/degree-diameter/research/frontier/build_haar2.py <file>`
   (must print VALID). For larger graphs do not run build_haar2.py; report the path and haar_sym's
   `full diameter check: OK` line (Opus checks it with the low-memory checkers).
4. After a solution, continue with the next group in the list (all are larger). Report every group's per-seed bests.
