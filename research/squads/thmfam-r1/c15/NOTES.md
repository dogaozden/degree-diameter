# c15 notes (single-orbit families, alpha of order k = 5 or 6 in PSL(2,q))

Generator: gen_c15.py. h = companion matrix [[0,-1],[1,t]] with the smallest t giving projective order k (k = 5 needs
q = +-1 mod 5 for the 10 primes used; k = 6 needs q = +-1 mod 12 for 11 primes). Shape 1: {I} u O(x), Delta = k+1.
Shape 2: O(x) u O(y), Delta = 2k. x, y fixed from {u,l,a,b,c} or random (--seed). Run log: results.log (run_all.sh).
Admissible primes: k=5: 29,31,41,59,61,71,79,89,101,109; k=6: 23,37,47,59,61,71,73,83,97,107,109.
All runs connected. Uniform x was chosen from 4-5 candidates scored on the same primes (selection bias, not held out).
Summary (mean_excess, lower is better):
- Delta 6: k=5 uniform 3.46-3.86; k=5 random 3.66-3.76; k=3 random 3.26-3.46 (Q5 list).
- Delta 7: k=6 uniform 3.70-4.80; k=6 random 3.98-4.34; k=3 random 3.07-3.34 (Q6 list).
- Delta 10: k=5 uniform 3.10; k=5 random 2.90-3.10; k=3 random 2.60-2.70 (Q5 list).
- Delta 12: k=6 uniform 2.73-3.27; k=6 random 2.91-3.09; k=3 random 2.55-2.64 (Q6 list).
