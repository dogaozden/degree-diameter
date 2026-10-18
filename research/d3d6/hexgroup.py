"""Automorphisms of H(5) (gh6 labels) from SL(3,q) acting as g on (x0,x1,x2), g^-T on (x4,x5,x6), x3 fixed.
perm_from_matrix(g) -> (point perm, line perm) or None if lines are not preserved."""
import json, sys, itertools
sys.path.insert(0, '../gh6'); import gh_build
q = 5
d = json.load(open('../gh6/hex/hexagon_q5.json'))
P = gh_build.quadric_points(q); L = d['lines']
pid = {tuple(p): i for i, p in enumerate(P)}
lid = {frozenset(l): j for j, l in enumerate(L)}


def inv3(g):
    a = g
    det = (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1]) - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
           + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])) % q
    di = pow(det, q - 2, q)
    adj = [[0]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            m = [[a[r][c] for c in range(3) if c != i] for r in range(3) if r != j]
            adj[i][j] = ((-1) ** (i + j)) * (m[0][0]*m[1][1]-m[0][1]*m[1][0])
    return [[(adj[i][j] * di) % q for j in range(3)] for i in range(3)], det


def perm_from_matrix(g, variant=0):
    gi, det = inv3(g)
    gt = [[gi[j][i] for j in range(3)] for i in range(3)]  # inverse transpose
    def act(v):
        a = [sum(g[i][k] * v[k] for k in range(3)) % q for i in range(3)]
        b = [sum(gt[i][k] * v[4 + k] for k in range(3)) % q for i in range(3)]
        w = a + [v[3]] + b
        return gh_build.normalize(w, q)
    pp = []
    for p in P:
        w = act(p)
        if w not in pid: return None
        pp.append(pid[w])
    lp = []
    for l in L:
        s = frozenset(pp[x] for x in l)
        if s not in lid: return None
        lp.append(lid[s])
    return pp, lp


if __name__ == '__main__':
    import random
    rng = random.Random(1); ok = 0
    for t in range(5):
        while True:
            g = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
            if inv3(g)[1] == 1: break
        r = perm_from_matrix(g); print('random SL3 element preserves lines:', r is not None)
