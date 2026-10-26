# raise-d8D9 round 3: beat the (8,9) record of 1,341,600 vertices

Job "raise3-8-9" (Haar worker, Haiku 5.5, 2026-10-26). Branch: claude/raise-d8d9-record-3-sqwtju.
Rounds 1 and 2 (claude/raise-d8d9-record-ogr1zr, claude/raise-d8d9-record-2-qz3qcj) ended with no new record.
Record: N = 670,800 (2N = 1,341,600), sl 25 x Z43. Target: any valid Haar graph with N >= 670,801.

## What round 2 tried (do not repeat)
- psl 47 x Z13 with ORBW=3 (2 h x 4 runs): stuck at cost 3 (involutions, odd D).
- sl 17 x Z139 (mu 34.7): stuck at 12-36.
- prod psl 5 x psl 7 x Z67, prod sl 4 x psl 7 x Z67, sl 13 x Z313, sl 8 x Z1333/Z1339, sl 7 x Z1999, sl 11 x Z511,
  sl 9 x Z937, psl 13 x Z619: screened, poor tails.
- k = 7 one-orbit structure (f = 1, m = 1): hopeless.

## Round 3 plan
1. Screen every window group with `tools/orb_screen.py 8 9 670801 690000 "3 2 2" --anyn`. Round 2 used the default
   filter (all prime factors of n = 1 mod 3), which silently dropped Z17, Z23, Z56, Z165, Z275, ...
2. Check |Fix(alpha)|. A composite cyclic factor with a prime p = 2 mod 3 forces alpha to be trivial on Z_p, and
   gcd(r-1, n) adds fixed points. sl 13 x Z308: |Fix| = 527, min 1026 in 200 samples. Ruled out.
3. Run the best survivors with the annealer on 4 cores.

## Screen results
(filled in below as they come in)
