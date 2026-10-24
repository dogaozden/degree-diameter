# Exhaustive check of "building coset graphs": side A = J-residues, side B = K-residues of a finite building
# with Coxeter system (W,S) and parameters q_s; R_A ~ R_B iff delta(R_A, R_B) lies in Omega, a union of
# (W_J, W_K)-double cosets. In a building the set of Weyl distances reachable by a walk with prescribed steps is
# the support of the corresponding product in the Iwahori-Hecke algebra (all structure constants are >= 0), so
#   diameter <= 5  iff  Omega o Omega^-1 o Omega o Omega^-1 = W  and  Omega^-1 o Omega o Omega^-1 o Omega = W,
# where X o Y = supp(1_X 1_Y). supp(T_x T_s) = {xs} if l(xs) > l(x), else {x, xs}.
# Degrees: deg_A(D) = wt(D)/P_K(q), deg_B(D) = wt(D)/P_J(q), wt(D) = sum_{x in D} q_x.
import itertools, math, sys
import numpy as np
from partflags import coxeter_matrix, tits, key

class Cox:
    def __init__(self, M):
        self.n = n = len(M)
        gens = tits(M)
        e = np.eye(n)
        idx = {key(e): 0}; mats = [e]; words = [()]
        frontier = [0]
        while frontier:
            nf = []
            for i in frontier:
                for s in range(n):
                    B = mats[i] @ gens[s]; k = key(B)
                    if k not in idx:
                        idx[k] = len(mats); mats.append(B); words.append(words[i] + (s,)); nf.append(idx[k])
            frontier = nf
        self.N = N = len(mats)
        self.words = words
        self.length = [len(w) for w in words]
        self.rmul = [[idx[key(mats[i] @ gens[s])] for s in range(n)] for i in range(N)]
        self.inv = [idx[key(np.linalg.inv(mats[i]))] for i in range(N)]
        self.mats = mats; self.idx = idx

    def wt(self, qs):
        return [math.prod(qs[s] for s in w) for w in self.words]

    def parab(self, I):
        I = set(I)
        return [i for i in range(self.N) if set(self.words[i]) <= I]

    def lmul_word(self, word, i):  # (s_1...s_k) * x
        # left multiplication via inverses: s x = (x^-1 s)^-1
        x = self.inv[i]
        for s in reversed(word):
            x = self.rmul[x][s]
        return self.inv[x]

    def supp_times_s(self, X, s):
        out = set()
        for x in X:
            xs = self.rmul[x][s]
            out.add(xs)
            if self.length[xs] < self.length[x]:
                out.add(x)
        return out

    def circ(self, X, Y):
        out = set()
        for y in Y:
            Z = set(X)
            for s in self.words[y]:
                Z = self.supp_times_s(Z, s)
            out |= Z
        return out

def double_cosets(C, J, K):
    WJ, WK = C.parab(J), C.parab(K)
    seen = [-1] * C.N; dcs = []
    for x in range(C.N):
        if seen[x] >= 0: continue
        D = set()
        for u in WJ:
            ux = C.lmul_word(C.words[u], x)
            for v in WK:
                y = ux
                for s in C.words[v]:
                    y = C.rmul[y][s]
                D.add(y)
        for y in D: seen[y] = len(dcs)
        dcs.append(sorted(D))
    return dcs

def analyse(name, M, qsets, DMAX=16, minverts=20000, out=sys.stdout):
    C = Cox(M)
    n = C.n
    S = list(range(n))
    found = []
    subsets = [tuple(c) for r in range(0, n + 1) for c in itertools.combinations(S, r)]
    for qs in qsets:
        wt = C.wt(qs)
        tot = sum(wt)
        P = {I: sum(wt[i] for i in C.parab(I)) for I in subsets}
        for J in subsets:
            for K in subsets:
                if J > K: continue
                nA, nB = tot // P[J], tot // P[K]
                if nA + nB < minverts or max(nA, nB) > 54241:
                    continue
                dcs = double_cosets(C, J, K)
                info = []
                for D in dcs:
                    w = sum(wt[x] for x in D)
                    dA, dB = w // P[K], w // P[J]
                    if dA <= DMAX and dB <= DMAX:
                        info.append((D, dA, dB))
                # all unions with total degree <= DMAX on both sides
                for r in range(1, len(info) + 1):
                    for comb in itertools.combinations(range(len(info)), r):
                        dA = sum(info[c][1] for c in comb); dB = sum(info[c][2] for c in comb)
                        if dA > DMAX or dB > DMAX: continue
                        Om = set().union(*[info[c][0] for c in comb])
                        Omi = {C.inv[x] for x in Om}
                        X2 = C.circ(Om, Omi)
                        X4 = C.circ(C.circ(X2, Om), Omi)
                        Y4 = C.circ(C.circ(C.circ(Omi, Om), Omi), Om)
                        okA, okB = len(X4) == C.N, len(Y4) == C.N
                        rec = (name, tuple(qs), J, K, dA, dB, nA, nB, len(X4), len(Y4), C.N)
                        if okA and okB:
                            print('D<=5 FOUND', rec, file=out, flush=True)
                            found.append(rec)
                        elif nA + nB > 31460:
                            print('  fail', rec, file=out, flush=True)
    return found

if __name__ == '__main__':
    pp = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16]
    jobs = []
    for n in range(2, 7):
        jobs.append(('A%d' % n, coxeter_matrix('A', n), [[q] * n for q in pp]))
    for n in range(2, 6):
        qsets = [[q] * n for q in pp] + [[q] * (n - 1) + [q * q] for q in pp] + [[q * q] * (n - 1) + [q] for q in pp] \
            + [[q * q] * (n - 1) + [q ** 3] for q in pp]
        jobs.append(('B%d' % n, coxeter_matrix('B', n), qsets))
    for n in (4, 5):
        jobs.append(('D%d' % n, coxeter_matrix('D', n), [[q] * n for q in pp]))
    jobs.append(('F4', coxeter_matrix('F', 4), [[q] * 4 for q in pp] + [[q, q, q * q, q * q] for q in pp]))
    jobs.append(('G2', coxeter_matrix('G', 2), [[q, q] for q in pp] + [[q, q ** 3] for q in pp] + [[q ** 3, q] for q in pp]))
    jobs.append(('I8', coxeter_matrix('I8', 2), [[q, q * q] for q in (2, 8)] + [[q * q, q] for q in (2, 8)]))
    which = sys.argv[1:] or [j[0] for j in jobs]
    for name, M, qsets in jobs:
        if name in which:
            print('==', name, flush=True)
            analyse(name, M, qsets)
