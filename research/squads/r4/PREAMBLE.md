# Squad round 4 preamble: small raises on the next rungs

Tools, rules, report format: `/home/user/degree-diameter/research/squads/r1/PREAMBLE.md` and `r2/PREAMBLE.md` (read the
Tools and Machine rules sections). Files only under `/home/user/degree-diameter/research/squads/r4/<your card>/`.
One heavy process at a time, under `timeout 1000 nice -n 10`. About 45 minutes in total, then report. No git, no edits
elsewhere, nothing left running.

## The task

Each card gets one or two cells and an explicit list of groups whose order is just above our record, with μ at most
~1.6 above the μ at which the record was solved. Use **the record's own structure** (ORBIT given per cell). These are
small steps (+0.1–1 %), so they should behave much like the record did. For each group, in the order given:

1. Seed 1 for the time given on your card: `ORBIT="<k m f>" timeout 1000 nice -n 10 $B/haar_sym d D SECS 1 8
   r4/<card>/<tag>_s1.txt GROUP n > r4/<card>/<tag>_s1.log 2>&1`.
2. If it ends at ≤ 6 uncovered, run seed 2 (and seed 3 if still ≤ 6). If it ends far above (> 20), move on.
3. A solution (`best=0`, `wrote ...`) above the record: for 2N ≤ 3,000,000 vertices run
   `python3 /home/user/degree-diameter/research/frontier/build_haar2.py <file>` (must print VALID). For larger graphs do
   NOT run build_haar2.py (too much memory); just report the file path and haar_sym's `full diameter check: OK` line,
   and Opus checks it with the low-memory checkers.
4. After a solution, move to the next group in your list only if it is larger.

Lessons so far: plateaus form early and depend on the group; when a run sits at the same value for its second half, a
longer run will not help, a new seed sometimes does.
