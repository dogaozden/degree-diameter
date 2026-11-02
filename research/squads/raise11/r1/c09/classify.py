import re, sys, collections
# usage: classify.py EVALOUT_FILE p n [g-spec]  ; EVALOUT from EVAL=... UNCPRINT=1 haar_big0
# element (M,z): M=[[a,b],[c,d]] mod p, z mod n. alpha = conj by g=[[0,-1],[1,-1]] (order 3) x (z -> r z)
p = int(sys.argv[2]); n = int(sys.argv[3])
def mul(X, Y):
    return ((X[0]*Y[0]+X[1]*Y[2])%p, (X[0]*Y[1]+X[1]*Y[3])%p,
            (X[2]*Y[0]+X[3]*Y[2])%p, (X[2]*Y[1]+X[3]*Y[3])%p)
g = (0, p-1, 1, p-1)
def comm(X, Y): return mul(X, Y) == mul(Y, X)
def classify(M, z, r_fixed_z0=True):
    a,b,c,d = M
    if b == 0 and c == 0 and a in (1, p-1) and d == a:
        return 'central(+-I,z)' if a == 1 or True else ''
    if M == (p-1,0,0,p-1): return 'central(+-I,z)'
    import os
    neg = lambda X: tuple((-x)%p for x in X)
    gM, Mg = mul(M,g), mul(g,M)
    psl = os.environ.get('PSL') == '1'
    if comm(M, g) or (psl and (gM == neg(Mg))):
        return 'alpha-fixed(torus of g, z=0)' if z == 0 else 'torus-of-g, z!=0'
    if (mul(M,M) == (1,0,0,1)): return 'involution-ish(M^2=I)'
    if (a + d) % p == 0 and (a*d - b*c) % p == 1: return 'trace0 (PSL involution class)'
    return 'generic'
rows = []
pat = re.compile(r'uncovered (\d+) mat\((\d+),(\d+),(\d+),(\d+)\) z=(\d+)(.*)')
for line in open(sys.argv[1]):
    m = pat.search(line)
    if not m: continue
    idx = int(m.group(1)); M = tuple(int(m.group(i)) for i in range(2,6)); z = int(m.group(6))
    side = 'B' if '(B side)' in m.group(7) else 'A'
    rows.append((idx, side, M, z, classify(M, z)))
cnt = collections.Counter((s, c) for _, s, _, _, c in rows)
tot = collections.Counter(c for _, _, _, _, c in rows)
for k in sorted(tot): print(f"{k}: {tot[k]}  (A {cnt[('A',k)]}, B {cnt[('B',k)]})")
print("total uncovered rows:", len(rows), " A:", sum(1 for r in rows if r[1]=='A'), " B:", sum(1 for r in rows if r[1]=='B'))
