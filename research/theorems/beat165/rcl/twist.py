# x-dependent directions: f_lam(x) = (A + lam N) x + lam b, N rank 1 (N x = (w.x) u), b not in span(u).
# For random 4-walks: number of distinct endpoints from x (out of 256), and closed-walk fiber coverage at a girth-6 vertex.
import random, sys
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def vec(i): return [(i >> (2*j)) & 3 for j in range(4)]
def idx(v): return v[0] | v[1] << 2 | v[2] << 4 | v[3] << 6
def mv(A, x):
    v = vec(x); return idx([MUL[A[i][0]][v[0]] ^ MUL[A[i][1]][v[1]] ^ MUL[A[i][2]][v[2]] ^ MUL[A[i][3]][v[3]] for i in range(4)])
def dot(w, x): v = vec(x); return MUL[w[0]][v[0]] ^ MUL[w[1]][v[1]] ^ MUL[w[2]][v[2]] ^ MUL[w[3]][v[3]]
def smul(s, x): return idx([MUL[s][c] for c in vec(x)])
def invertible(A): return len({mv(A, x) for x in range(256)}) == 256
def randmat():
    while True:
        A = [[random.randrange(4) for _ in range(4)] for _ in range(4)]
        if invertible(A): return A
class Fam:
    def __init__(self, twisted):
        while True:
            self.A = randmat(); self.b = random.randrange(1, 256)
            if twisted:
                self.u = random.randrange(1, 256); self.w = [random.randrange(4) for _ in range(4)]
                if all(self.b != smul(s, self.u) for s in range(4)) and any(self.w):
                    ok = True
                    for lam in range(4):
                        M = [[self.A[i][j] ^ MUL[lam][MUL[self.w[j]][vec(self.u)[i]]] for j in range(4)] for i in range(4)]
                        if not invertible(M): ok = False
                    if ok: break
            else:
                self.u = 0; self.w = [0, 0, 0, 0]; break
        self.fwd = [[0]*4 for _ in range(256)]
        for x in range(256):
            d = self.b ^ smul(dot(self.w, x), self.u)   # direction N x + b
            ax = mv(self.A, x)
            for lam in range(4): self.fwd[x][lam] = ax ^ smul(lam, d)
        self.bwd = [[] for _ in range(256)]
        for x in range(256):
            for lam in range(4): self.bwd[self.fwd[x][lam]].append(x)
def endpoints(fams, x):
    S = {x}
    for f, forward in fams:
        S = {y for z in S for y in (f.fwd[z] if forward else f.bwd[z])}
    return S
random.seed(int(sys.argv[1]))
for twisted in (False, True):
    cnts = []
    for t in range(200):
        fams = [(Fam(twisted), True) for _ in range(4)]
        x = random.randrange(256); cnts.append(len(endpoints(fams, x)))
    print('twisted' if twisted else 'translate', '4-walk distinct endpoints: mean %.1f, =256: %d/200, hist' % (sum(cnts)/len(cnts), sum(1 for c in cnts if c == 256)),
          sorted(set(cnts))[:8], '...')
    # closed-walk coverage at a girth-6 vertex c with 4 edges (2 out, 2 in), each neighbour with 3 further edges
    covs = []
    for t in range(40):
        E = [(Fam(twisted), random.random() < 0.5) for _ in range(4)]   # edge at c: (family, c is the tail)
        NB = [[(Fam(twisted), random.random() < 0.5) for _ in range(3)] for _ in range(4)]
        x = random.randrange(256); U = {x}
        for i, (f, out) in enumerate(E):
            go = (f, out); back = (f, not out)
            U |= endpoints([go, back], x)
            for j, (g, out2) in enumerate(E): U |= endpoints([go, back, (g, out2), (g, not out2)], x)
            for (g, out2) in NB[i]: U |= endpoints([go, (g, out2), (g, not out2), back], x)
        covs.append(len(U))
    print('   closed-walk coverage of the fiber (girth-6 vertex): mean %.1f max %d full %d/40' % (sum(covs)/len(covs), max(covs), sum(1 for c in covs if c == 256)))
