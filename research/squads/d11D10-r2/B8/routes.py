# B8 (constructions wildcard): counting bounds for non-search routes to (11,10).
# Pure arithmetic, no graph is built. Per side = one colour class of a balanced bipartite graph.
from itertools import product
from math import comb

def walks_odd(d, D):
    # B-side Moore count for diameter D even: vertices at odd distance <= D-1 from an A-vertex
    return sum(d * (d - 1) ** (l - 1) for l in range(1, D, 2))

def same_side_ball(d, r):
    # vertices at even distance <= r from a vertex (incl. itself)
    return 1 + sum(d * (d - 1) ** (l - 1) for l in range(2, r + 1, 2))

def moore_total_even(d, D):          # bipartite Moore bound, D even: 2 * W
    return 2 * walks_odd(d, D)

def moore_total_odd(d, D):           # bipartite Moore bound, D odd: 2 * min(even-ball(D-1), odd-ball(D))
    return 2 * min(same_side_ball(d, D - 1), walks_odd(d, D + 1))

W11 = walks_odd(11, 10)
print("W(11,10) per side =", W11, " Moore total =", moore_total_even(11, 10))
HAAR11 = 148_729_680
print("ours (11,10): 148,729,680 = %.2f%% of Moore" % (100 * HAAR11 / moore_total_even(11, 10)))
print("table (11,10): 130,592,354 = %.2f%% of Moore" % (100 * 130_592_354 / moore_total_even(11, 10)))
print("target 157,835,304 = %.2f%% of Moore" % (100 * 157_835_304 / moore_total_even(11, 10)))

# 1. Abelian (single-fibre cyclic / bi-circulant) Haar graphs: endpoints of odd walks of length <= 9 are
#    sum_i c_i s_i with c in Z^11, sum c_i = 1, |c|_1 <= 9. Abelian => at most this many distinct B-elements.
def count_c(d, rmax):
    # number of c in Z^d with sum c = 1 and sum |c_i| <= rmax, by DP over coordinates
    # state: (sum_so_far, abs_so_far) -> count
    dp = {(0, 0): 1}
    for _ in range(d):
        nd = {}
        for (s, a), v in dp.items():
            for x in range(-rmax, rmax + 1):
                a2 = a + abs(x)
                if a2 > rmax:
                    continue
                key = (s + x, a2)
                nd[key] = nd.get(key, 0) + v
        dp = nd
    return sum(v for (s, a), v in dp.items() if s == 1 and a <= rmax)

M_ab11 = count_c(11, 9)
print("abelian single-fibre bound, d=11, D=10: B-side <= %d per side (table per side 65,296,177)" % M_ab11)
M_ab10 = count_c(10, 9)
print("abelian single-fibre bound, d=10, D=10: <= %d per side" % M_ab10)

# 2. Blow-up (Delorme-type copies of vertices with identical neighbourhoods). A base of degree d0 with
#    per-vertex copy multiplicities m satisfies sum_{b in N(a)} m_b <= 11; the fractional bound is total*11/d0.
print("\nBlow-up route: n(11,10) >= (11/d0) * n(d0,10) at best; needed base total = 148,729,680 * d0 / 11")
our = {10: 57_868_272, 8: 7_349_616, 7: 1_993_920, 6: 462_840}
for d0 in (10, 9, 8, 7):
    need = HAAR11 * d0 / 11
    mt = moore_total_even(d0, 10)
    rec = our.get(d0)
    line = "d0=%2d: need base total >= %13.0f = %5.1f%% of (%d,10) Moore %d" % (d0, need, 100 * need / mt, d0, mt)
    if rec:
        line += " | our record %d -> blow-up bound %.0f (%.1f%% of 148.7M)" % (rec, rec * 11 / d0, 100 * rec * 11 / d0 / HAAR11)
    print(line)
print("d0 = 10 with copies on both sides (A-copies and B-copies, each side N/10): factor 1.1, not 11/10 * ... ok")

# 3. Odd-diameter product K_2 x H, H bipartite (10,9): total = 2 * total(H).
mt9 = moore_total_odd(10, 9)
print("\nK2 x H route: (10,9) Moore total =", mt9, "; needed total(H) >=", HAAR11 // 2,
      "= %.1f%% of it" % (100 * (HAAR11 / 2) / mt9))
mt89 = moore_total_odd(8, 9)
print("  for reference our (8,9) record 1,130,880 is %.1f%% of its Moore total %d" % (100 * 1130880 / mt89, mt89))

# 4. Lifts / random-model mu for a group (per side) N with W = 1,111,111,111: mu = N exp(-W/N)
import math
def mu(N, W=W11):
    return N * math.exp(-W / N)
for label, N in [("ours 74,364,840", 74_364_840), ("target 78,917,652", 78_917_652),
                 ("Z2 lift of ours (148,729,680)", 148_729_680), ("table 65,296,177", 65_296_177)]:
    print("random-model mu at N = %s: %.4g" % (label, mu(N)))

# 5. Cartesian products (degrees a + b = 11, diameters D1 + D2 = 10): vertex count multiplies, Moore counts multiply.
best = (0, None)
for a in range(1, 11):
    b = 11 - a
    for D1 in range(1, 10):
        D2 = 10 - D1
        ta = moore_total_even(a, D1) if D1 % 2 == 0 else moore_total_odd(a, D1)
        tb = moore_total_even(b, D2) if D2 % 2 == 0 else moore_total_odd(b, D2)
        if ta * tb > best[0]:
            best = (ta * tb, (a, D1, b, D2))
print("\nCartesian product: largest product of Moore totals over all splits = %d at (a,D1,b,D2) = %s" % best)
