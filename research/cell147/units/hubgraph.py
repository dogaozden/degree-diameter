"""Hub graphs from Singer difference sets: line-side hub j ~ point-side hub k iff (k - j) mod v in the set.
Any two line-side hubs then share exactly one point-side neighbour and vice versa (projective plane incidence).
Usage: python3 hubgraph.py r K > extras   (PG(2,r), r in {2,3,4,5,7,8,9}; uses hubs of the first K units, K <= r^2+r+1;
       unit i: line-side hub 2i, point-side hub 2i+1). Output in the uhcheck EXTRAS format with NS = 0."""
import sys
DS = {2: [0, 1, 3], 3: [0, 1, 3, 9], 4: [0, 1, 4, 14, 16], 5: [0, 1, 3, 8, 12, 18], 7: [0, 1, 3, 13, 32, 36, 43, 52],
      8: [0, 1, 3, 7, 15, 31, 36, 54, 63], 9: [0, 1, 3, 9, 27, 49, 56, 61, 77, 81]}
r, K = int(sys.argv[1]), int(sys.argv[2]); v = r * r + r + 1; S = DS[r]
diffs = sorted((a - b) % v for a in S for b in S if a != b)
assert diffs == list(range(1, v)), 'not a difference set'
assert K <= v
E = [(2 * j, 2 * ((j + s) % v) + 1) for j in range(K) for s in S if (j + s) % v < K]
print(0)
for a, b in E: print(a, b)
