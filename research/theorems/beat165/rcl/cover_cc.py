# c = d coverage at a girth-6 controller vertex with translate families: sets E (difference sets D = L + L, in c's frame).
# Sets: E_e (4 edges at c), E_e + E_f (pairs incl. e = f), E_e + T_e(E'_g) (3 other edges g at each neighbour).
import random, itertools, sys
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def vec(i): return [(i >> (2*j)) & 3 for j in range(4)]
def idx(v): return v[0] | v[1] << 2 | v[2] << 4 | v[3] << 6
def add(a, b): return a ^ b
def matvec(A, x):
    v = vec(x); return idx([MUL[A[i][0]][v[0]] ^ MUL[A[i][1]][v[1]] ^ MUL[A[i][2]][v[2]] ^ MUL[A[i][3]][v[3]] for i in range(4)])
def randmat():
    while True:
        A = [[random.randrange(4) for _ in range(4)] for _ in range(4)]
        if len({matvec(A, x) for x in range(256)}) == 256: return A
def line(b): return {idx([MUL[l][c] for c in vec(b)]) for l in range(4)}
def dset(L): return {a ^ b for a in L for b in L}
def randline(): return dset(line(random.randrange(1, 256)))
def randrich():
    while True:
        L = [0] + random.sample(range(1, 256), 3)
        D = dset(L)
        if len(D) == 7: return D
def sumset(X, Y): return {a ^ b for a in X for b in Y}
def trial(nrich_c, nrich_nb):
    # edges at c: first nrich_c rich; each neighbour w_e: the edge back to c is e itself (same type), plus 3 others,
    # of which (nrich_nb - [e rich]) are rich (each vertex has nrich_nb rich edges in total, nrich_c = nrich_nb)
    E = [randrich() if i < nrich_c else randline() for i in range(4)]
    sets = [{0}] + E
    for i in range(4):
        for j in range(i, 4): sets.append(sumset(E[i], E[j]))
    for i in range(4):
        T = randmat(); others = nrich_nb - (1 if i < nrich_c else 0)
        for g in range(3):
            Eg = randrich() if g < others else randline()
            sets.append(sumset(E[i], {matvec(T, y) for y in Eg}))
    U = set().union(*sets); return len(U)
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
for r in (0, 1, 2, 3, 4):
    res = [trial(r, r) for _ in range(300)]
    print(f'rich edges per vertex {r}: coverage max {max(res)}, mean {sum(res)/len(res):.1f}, full {sum(1 for x in res if x == 256)}/300')
