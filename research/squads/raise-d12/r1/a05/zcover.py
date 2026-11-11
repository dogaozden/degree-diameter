# a05: z-projection ceiling. Words of length <= D-1 = 11 in S = {e, fixed (z=0), x, alpha x, alpha^2 x} (z-values c, r c, r^2 c);
# the Z_n coordinate of a word is c*(n1 + r n2 + r^2 n3) mod n, with n1+n2+n3 <= 11 (e and z=0 letters pad). Coverage needs all n residues.
import sys
L = 11
def reach(n, r):
    vals = set()
    for a in range(L + 1):
        for b in range(L + 1 - a):
            for c in range(L + 1 - a - b):
                vals.add((a + r * b + r * r * c) % n)
    return len(vals)
r = 8  # (4,12) case: z -> 8z on Z_73, order 3
print("n=73 r=8 reachable:", reach(73, 8), "of 73")
print("n=1063 r=343 (3 1 2 card): reachable", reach(1063, 343), "of 1063; multiset bound C(14,3) =", 364)
best = 0
for n in range(2, 2000):
    for rr in range(2, n):
        if pow(rr, 3, n) == 1 and rr * rr % n + rr % n + 1 >= 0 and len({rr, rr*rr % n}) == 2 and n > 1:
            if reach(n, rr) == n:
                best = max(best, n)
            break
print("largest n <= 2000 with full Z_n coverage for some order-3 r:", best)
