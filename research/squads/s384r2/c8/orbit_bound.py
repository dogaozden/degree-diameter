# Counting bound for orbit splits of a bipartite graph with max degree 6, diameter 5, all orbits of size m.
# Side X with b orbits, side Y with a orbits. Same-side ball radius 4 of v (deg d, max deg of other side DT,
# max deg of own side DS) has at most 1 + d(DT-1) + d(DT-1)^2 (DS-1) vertices. Every same-side vertex must lie in it,
# so each side needs (orbits on that side)*m <= ball bound for its smallest-degree orbit.
import itertools, sys
def ball(d, DT, DS):
    return 1 + d*(DT-1) + d*(DT-1)**2*(DS-1)
def max_m(a, b):
    best = (0, None)
    for al in itertools.product(range(1,7), repeat=a):
        for be in itertools.product(range(1,7), repeat=b):
            if sum(al) != sum(be):
                continue
            aM, bM = max(al), max(be)
            # m feasible iff b*m <= min_j ball(beta_j; DT=aM, DS=bM) and a*m <= min_i ball(alpha_i; DT=bM, DS=aM)
            mx = min(ball(x, aM, bM) for x in be) // b
            mx = min(mx, min(ball(x, bM, aM) for x in al) // a)
            if mx > best[0]:
                best = (mx, (al, be))
    return best
for a, b in [(1,1),(1,2),(2,2),(2,3),(1,3),(3,3),(3,4)]:
    m, degs = max_m(a, b)
    print(f"split {a}+{b}: max m allowed by counting = {m}, N_max = {(a+b)*m}, example degrees (side A {degs[0] if degs else None}, side B {degs[1] if degs else None})" if degs else f"split {a}+{b}: infeasible")
