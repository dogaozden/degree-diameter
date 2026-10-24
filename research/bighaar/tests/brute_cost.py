"""Independent brute-force cost of a Haar graph H(G,S), G = SL(2,p) or PSL(2,p) x Z_n, read from a haar_gen3-format file:
cost = number of g in G with (g,B) not within distance D-1 of (e,A); edges (g,A) ~ (s g, B).  Plain BFS on explicit
elements (tuples), no shared code with haar_big.c.  usage: python3 brute_cost.py SOL"""
import sys, re
lines = [l for l in open(sys.argv[1]).read().split("\n") if l.strip()]
h = lines[0].split(); d, D, fam, p, n = int(h[0]), int(h[1]), h[2], int(h[3]), int(h[5])
def norm(m):
    a, b, c, dd = (x % p for x in m)
    if fam == "psl":
        f = a if a else c
        if f > (p - 1) // 2: a, b, c, dd = (-a) % p, (-b) % p, (-c) % p, (-dd) % p
    return (a, b, c, dd)
S = []
for l in lines[1:1 + d]:
    a, b, c, dd = map(int, re.search(r"mat\((\d+),(\d+),(\d+),(\d+)\)", l).groups()); z = int(re.search(r"z=(\d+)", l).group(1))
    S.append((norm((a, b, c, dd)), z % n))
def mul(x, y):
    (a, b, c, dd), z = x; (e, f, g, hh), w = y
    return (norm((a * e + b * g, a * f + b * hh, c * e + dd * g, c * f + dd * hh)), (z + w) % n)
def inv(x):
    (a, b, c, dd), z = x
    return (norm((dd, -b, -c, a)), (-z) % n)
SI = [inv(s) for s in S]
e = ((1, 0, 0, 1), 0)
order = p * (p * p - 1) // (2 if fam == "psl" else 1) * n
seen = [{e}, set()]; frontier = {e}; side = 0
for step in range(1, D):
    nxt = set()
    for x in frontier:
        for s in (S if side == 0 else SI):
            y = mul(s, x)
            if y not in seen[1 - side]: seen[1 - side].add(y); nxt.add(y)
    frontier = nxt; side ^= 1
print("BRUTE cost=%d order=%d" % (order - len(seen[1]), order))
