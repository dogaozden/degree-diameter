import sys, numpy as np
# G = (Z7 x|_2 Z3) x (Z173 x|_16 Z43); element index -> (a1,j1,a2,j2)
m1,k1,r1 = 7,3,2
m2,k2,r2 = 173,43,16
conv = int(sys.argv[2]) if len(sys.argv)>2 else 1   # 1: (a,j)(b,l)=(a+r^j b, j+l); -1: r^-j
def pw(r,j,m): return pow(r,j,m) if j>=0 else pow(pow(r,-1,m),-j,m)
def rj(r,j,m,c):
    return pow(r, (j*c) % (m-1) if False else 0, m)  # placeholder
N1,N2 = m1*k1, m2*k2
N = N1*N2
idx = np.arange(N)
a1 = (idx // (k1*N2)) % m1; j1 = (idx // N2) % k1
a2 = (idx // k2) % m2; j2 = idx % k2
# precompute power tables
R1 = np.array([pow(r1, (j*conv) % k1, m1) for j in range(k1)])  # r1^(conv*j); order of r1 mod 7 is 3
R2 = np.array([pow(r2, (j*conv) % k2, m2) for j in range(k2)])
def enc(A1,J1,A2,J2):
    return ((A1*k1 + J1)*m2 + A2)*k2 + J2
def mul_all(g, s):
    # returns index array of s*g for all g in group (s given as tuple)  -- s*g
    b1,l1,b2,l2 = s
    A1 = (a1 + R1[j1]*0) # placeholder
    return None
def left_mult_index(s):
    b1,l1,b2,l2 = s
    # (s)(g): component: (b1 + r^{l1} * a1, l1 + j1)
    A1 = (b1 + R1[l1] * a1) % m1; J1 = (l1 + j1) % k1
    A2 = (b2 + R2[l2] * a2) % m2; J2 = (l2 + j2) % k2
    return enc(A1,J1,A2,J2)
def inv(s):
    b1,l1,b2,l2 = s
    # inverse of (b,l): (-r^{-l} b, -l)
    rinv1 = pow(r1, -1, m1); rinv2 = pow(r2, -1, m2)
    ia1 = (-pow(rinv1, (l1*conv)%k1, m1) * b1) % m1 if True else 0
    ia2 = (-pow(rinv2, (l2*conv)%k2, m2) * b2) % m2
    return ((ia1, (-l1)%k1, ia2, (-l2)%k2))
def mul(s,t):
    b1,l1,b2,l2 = s; c1,n1,c2,n2 = t
    return ((b1 + pow(r1,(l1*conv)%k1,m1)*c1)%m1, (l1+n1)%k1, (b2 + pow(r2,(l2*conv)%k2,m2)*c2)%m2, (l2+n2)%k2)
def parse(path):
    lines = open(path).read().split('\n')
    S=[]
    for ln in lines[1:]:
        if not ln.strip(): continue
        p = ln.split()
        if 'prod' not in ln: continue
        import re
        ms = re.findall(r'meta\(a=(\d+),j=(\d+)\)', ln)
        (x1,y1),(x2,y2) = ms
        S.append((int(x1),int(y1),int(x2),int(y2)))
    return S
S = parse(sys.argv[1])
print("S", S, "conv", conv)
e=(0,0,0,0)
def ball(P, steps):
    # set of products of <= steps elements of P (P contains e), via left mult
    mask = np.zeros(N,bool); cur = np.zeros(N,bool); cur[enc(0,0,0,0)] = True
    mask |= cur
    for _ in range(steps):
        nxt = np.zeros(N,bool)
        ids = np.nonzero(cur)[0]
        for p in P:
            Lp = left_mult_index(p)
            nxt[Lp[ids]] = True
        cur = nxt; mask |= cur
    return mask
PA = list({mul(inv(t), s) for s in S for t in S})
PB = list({mul(t, inv(s)) for s in S for t in S})
bA = ball(PA, 5); bB = ball(PB, 5)
print("|P|",len(PA),len(PB),"uncovered A",int((~bA).sum()),"B",int((~bB).sum()),"cost",int((~bA).sum()+(~bB).sum()))
for name,mk in (("A",~bA),("B",~bB)):
    for ix in np.nonzero(mk)[0][:10]:
        print(name, "hole", int(ix), (int(a1[ix]),int(j1[ix]),int(a2[ix]),int(j2[ix])), "order-ish inv", inv((int(a1[ix]),int(j1[ix]),int(a2[ix]),int(j2[ix]))))
