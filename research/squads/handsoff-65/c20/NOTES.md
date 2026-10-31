# c20 notes (downward surgery from near misses above 684)

Card: go DOWN from graphs above 686 with few far pairs (720 Haar near miss, 704 lift, 732 graph), delete vertices, repair
degrees, local search at fixed n >= 686. Target bad 0.

## Files
- analyze.py: all-pairs BFS, far-pair structure (`python3 analyze.py EDGES`, 0.5 s at n=720).
- dsa.c / dsa: DOWNWARD SA. env INFILE, DELA / DELB (vertices deleted from side A / side B), DELMODE greedy|rand
  (greedy: exact cost after each candidate deletion, SAMPLE candidates per step), SECS, T0, T1, SEED, OUT, TARGET.
  Moves: 2-switch (degree-preserving), greedy ADD between deficient opposite-side vertices (never raises cost).
  Max degree 6 is kept; deficits left after deletion are filled by ADD.
  Cost = unordered pairs at distance > 5 (bit-parallel BFS, ~0.3 ms per evaluation at n=720, ~3000 moves/s).

## Structure of the 720 Haar near miss (c6/h360_53.edges, SmallGroup(360,53), bad 360)
- All 360 far pairs are at distance exactly 6, all inside one side (vertices 360..719). Every vertex of that side has exactly
  2 far partners (a 2-regular graph, union of cycles); the other side has none. So the defect is one-sided: same-side
  even distances 6 instead of <= 4. Covering all 360 by deleting vertices would need about 180 vertices (n ~ 540): not
  possible inside 686..720; only rewiring can fix it.
