# aut_gen.py m k r s TABLE.bin AUT.bin : full automorphism group of G = <a,b | a^m, b^k=a^s, b a b^-1 = a^r>
# (element a^i b^j has index i + m*j). An automorphism is (x,y) = (image of a, image of b) satisfying the defining
# relations (von Dyck) and generating G. Writes TABLE.bin (nonsplit.py format) and AUT.bin (int32 count, count*N int32).
import sys, numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/w20")
import nonsplit
m, k, r, s = map(int, sys.argv[1:5])
T = nonsplit.table(m, k, r, s).astype(np.int64)   # T[x,y] = x*y
N = m * k
nonsplit.write_bin(T.astype(np.uint16), sys.argv[5])
ident = 0
def vpow(e):
    res = np.zeros(N, dtype=np.int64); base = np.arange(N, dtype=np.int64)
    while e:
        if e & 1: res = T[res, base]
        base = T[base, base]; e >>= 1
    return res
inv = np.array([int(np.where(T[g] == ident)[0][0]) for g in range(N)], dtype=np.int64)
pm, pk, ps, pr = vpow(m), vpow(k), vpow(s), vpow(r)
assert np.all(T[np.arange(N), inv] == ident)
auts = []
ys = np.arange(N, dtype=np.int64)
for x in range(N):
    if pm[x] != ident: continue
    yx = T[ys, x]                       # y*x
    yxyi = T[yx, inv[ys]]               # y*x*y^-1
    ok = (pk[ys] == ps[x]) & (yxyi == pr[x])
    for y in np.nonzero(ok)[0]:
        y = int(y)
        Px = [0] * m; cur = 0
        for i in range(m): Px[i] = cur; cur = int(T[cur, x])
        Py = [0] * k; cur = 0
        for j in range(k): Py[j] = cur; cur = int(T[cur, y])
        phi = np.empty(N, dtype=np.int64)
        for j in range(k):
            phi[j * m:(j + 1) * m] = T[np.array(Px), Py[j]]
        if len(np.unique(phi)) == N: auts.append(phi)   # bijective hom = automorphism
A = np.array(auts, dtype=np.int32)
with open(sys.argv[6], "wb") as f:
    np.array([len(auts)], dtype=np.int32).tofile(f)
    A.tofile(f)
print("N=%d |Aut|=%d" % (N, len(auts)))
