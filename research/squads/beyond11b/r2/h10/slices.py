# Uncovered-set anatomy for ORBIT "3 1 1" on Frobenius Z_p x| Z_k (haar graph, D = 11, S = {e, x, ux, u^2 x}).
import sys, collections
p, k, r, u, D = 1321, 11, 925, 1023, 11
N = p * k
def idx(a, j): return a * k + j
def mul(s, g):  # (a,j)(b,l) = (a + r^j b, j + l)
    a, j = divmod(s, k); b, l = divmod(g, k)
    return idx((a + pow(r, j, p) * b) % p, (j + l) % k)
def inv(s):
    a, j = divmod(s, k)
    ri = pow(r, (-j) % (p - 1), p)
    return idx((-ri * a) % p, (-j) % k)
e = idx(0, 0)
def run(x):
    S = [e, x, idx(u * divmod(x, k)[0] % p, divmod(x, k)[1]), idx(u * u * divmod(x, k)[0] % p, divmod(x, k)[1])]
    Si = [inv(s) for s in S]
    dA = [-1] * N; dB = [-1] * N
    dA[e] = 0; frontier = [('A', e)]; dist = 0
    # BFS on 2N vertices: (g,A)->(s g,B) ; (h,B)->(s^-1 h,A)
    dist_arr = {'A': dA, 'B': dB}
    fr = [('A', e)]; d = 0
    while fr and d < D:
        nf = []
        for side, g in fr:
            if side == 'A':
                for s in S:
                    h = mul(s, g)
                    if dB[h] < 0: dB[h] = d + 1; nf.append(('B', h))
            else:
                for si in Si:
                    h = mul(si, g)
                    if dA[h] < 0: dA[h] = d + 1; nf.append(('A', h))
        fr = nf; d += 1
    unA = [g for g in range(N) if dA[g] < 0]
    # B-side from (e,B) for odd D
    dB2 = [-1] * N; dA2 = [-1] * N; dB2[e] = 0; fr = [('B', e)]; d = 0
    while fr and d < D:
        nf = []
        for side, g in fr:
            if side == 'B':
                for si in Si:
                    h = mul(si, g)
                    if dA2[h] < 0: dA2[h] = d + 1; nf.append(('A', h))
            else:
                for s in S:
                    h = mul(s, g)
                    if dB2[h] < 0: dB2[h] = d + 1; nf.append(('B', h))
        fr = nf; d += 1
    unB = [g for g in range(N) if dB2[g] < 0]
    return S, unA, unB
x = idx(1, 1)
S, unA, unB = run(x)
print("x=(1,1) cost A-side", len(unA), "B-side", len(unB), "total", len(unA) + len(unB))
print("uncovered A by slice j:", sorted(collections.Counter(g % k for g in unA).items())[:11])
print("uncovered B by slice j:", sorted(collections.Counter(g % k for g in unB).items())[:11])
print("uncovered A by a-value (first 10):", sorted(divmod(g, k)[0] for g in unA)[:10], "count", len(unA))
