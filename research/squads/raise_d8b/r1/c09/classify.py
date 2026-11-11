# Classify uncovered holes from haar_big0 EVAL output (PSL(2,p) x Z_n, alpha = conj by g, z -> r z).
import sys, re, collections
P = int(sys.argv[2]) if len(sys.argv) > 2 else 79
g = ((0, P-1), (1, P-1))          # [[0,-1],[1,-1]]
ginv = ((P-1, 1), (P-1, 0))      # [[d,-b],[-c,a]] with det 1
def mul(x, y):
    return (((x[0][0]*y[0][0]+x[0][1]*y[1][0]) % P, (x[0][0]*y[0][1]+x[0][1]*y[1][1]) % P),
            ((x[1][0]*y[0][0]+x[1][1]*y[1][0]) % P, (x[1][0]*y[0][1]+x[1][1]*y[1][1]) % P))
def neg(x): return tuple(tuple((-v) % P for v in r) for r in x)
I = ((1, 0), (0, 1))
def same_pm(x, y): return x == y or x == neg(y)
def order_pm(x):
    y = x
    for k in range(1, 2*P+2):
        if same_pm(y, I): return k
        y = mul(y, x)
    return -1
pat = re.compile(r"uncovered \d+ mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\) z=(-?\d+)(.*)")
cls = collections.Counter(); rows = []
for line in open(sys.argv[1]):
    m = pat.search(line)
    if not m: continue
    a, b, c, d, z = map(int, m.groups()[:5]); side = "B" if "(B side)" in m.group(6) else "A"
    M = ((a % P, b % P), (c % P, d % P))
    gM = mul(g, M); Mg = mul(M, g)
    alpha_fixed = same_pm(mul(gM, ginv), M)          # g M g^-1 = +-M
    torus = (gM == Mg)                                # commutes with g exactly
    anti = (gM == neg(Mg))                            # g M g^-1 = -M
    o = order_pm(M)
    t2 = ((a + d) * (a + d)) % P                      # trace^2 mod p (sign-invariant)
    tc = "tr=0" if (a + d) % P == 0 else ("tr^2=1" if t2 == 1 else ("tr^2=4" if t2 == 4 else "tr^2=other"))
    zc = "z0" if z == 0 else "z!=0"
    key = (side, zc, "alphaFix" if alpha_fixed else "notAlphaFix", "torus" if torus else ("anti-g" if anti else "-"), "ord%d" % o, tc)
    cls[key] += 1; rows.append((side, z, M, o, tc, alpha_fixed, torus))
print("holes listed:", len(rows))
for k, v in sorted(cls.items(), key=lambda kv: -kv[1]): print(v, *k)
