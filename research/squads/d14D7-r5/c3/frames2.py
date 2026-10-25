import sys, time, random
sys.argv=['x']
src = open('octo_g2.py').read().split("closed = all")[0]
exec(src)
U_imag = sorted(X for X in S if X[0] == 0)
U_signed = sorted(tuple(2 * s if t == i else 0 for t in range(8)) for i in range(1, 8) for s in (1, -1))
def dot4(X, Y): return sum(a * b for a, b in zip(X, Y))
def closure(gens, cap=20000):
    I = np.eye(7, dtype=np.int64)
    seen = {I.tobytes(): I}; frontier = [I]
    G = [np.array(g, dtype=np.int64) for g in gens]
    while frontier:
        nf = []
        for X in frontier:
            for g in G:
                Y = (X @ g) % 11
                k = Y.tobytes()
                if k not in seen:
                    seen[k] = Y; nf.append(Y)
                    if len(seen) > cap: return None
        frontier = nf
    return seen
# exact frame search: F = 2f (integer), products checked as omul(F_i,F_j) == 2*s*F_k  (since omul = 4 f_i f_j)
def frames_exact(C):
    Cset=set(C); out=[]
    for F1 in C:
        for F2 in C:
            if dot4(F1,F2)!=0: continue
            P=omul(F1,F2)
            if any(p%2 for p in P): continue
            k,s=tab[(1,2)]
            F3=tuple(s*p//2 for p in P)
            if F3 not in Cset: continue
            for F4 in C:
                if dot4(F4,F1) or dot4(F4,F2) or dot4(F4,F3): continue
                F={1:F1,2:F2,3:F3,4:F4}; ok=True
                for m in (5,6,7):
                    i,j=next((i,j) for i in range(1,5) for j in range(1,5) if i!=j and tab[(i,j)][0]==m)
                    s=tab[(i,j)][1]; P=omul(F[i],F[j])
                    if any(p%2 for p in P): ok=False; break
                    Fm=tuple(s*p//2 for p in P)
                    if Fm not in Cset: ok=False; break
                    F[m]=Fm
                if not ok: continue
                for i in range(1,8):
                    for j in range(1,8):
                        if i==j: continue
                        k,s=tab[(i,j)]
                        if omul(F[i],F[j]) != tuple(2*s*x for x in F[k]): ok=False; break
                    if not ok: break
                if ok: out.append(tuple(F[i] for i in range(1,8)))
    return out
t0=time.time()
fr=frames_exact(U_imag)
print('frames in 126 Coxeter-imag units:', len(fr), round(time.time()-t0,1),'s', flush=True)
fr0=frames_exact(U_signed)
print('signed frames:', len(fr0), flush=True)
# group order check: closure of matrices mod 11 (M = F/2 -> F*6 mod 11)
def tomod(Fc): return np.array([[(Fc[c][r+1]*6)%11 for c in range(7)] for r in range(7)],dtype=np.int64)
allm=[tomod(F) for F in fr]
keys=set(m.tobytes() for m in allm)
print('distinct matrices:', len(keys), flush=True)
rng=random.Random(3)
for trial in range(5):
    gens=[rng.choice(allm) for _ in range(2)]
    H=closure(gens, cap=20000)
    print('closure of 2 random frames:', None if H is None else len(H), flush=True)
