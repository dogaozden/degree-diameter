# A(Δ,D): number of c in Z^Δ with sum(c) = eps (1 for D even, 0 for D odd) and |c|_1 <= D-1.
# Count by DP over coordinates: state (sum, l1).
from functools import lru_cache
import sys
def A(d, D):
    L = D - 1; eps = 1 if D % 2 == 0 else 0
    # ways[s][l] after processing coordinates
    from collections import defaultdict
    ways = defaultdict(int); ways[(0, 0)] = 1
    for _ in range(d):
        nw = defaultdict(int)
        for (s, l), w in ways.items():
            for c in range(-(L - l), L - l + 1):
                nw[(s + c, l + abs(c))] += w
        ways = nw
    return sum(w for (s, l), w in ways.items() if s == eps)
def W(d, D):
    return sum((d - 1) ** j for j in range(D))
if __name__ == "__main__":
    print("A(8,8) =", A(8, 8), " W(8,8) =", W(8, 8))
    for D in (8, 9, 10):
        print("D =", D, " ".join(f"{d}:{A(d,D)}" for d in range(3, 17)))
