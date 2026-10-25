"""W(E7) mod q acting on H(q) points: reflections in roots (roots = pickled list), root subsystems by DFS, orbits."""
import numpy as np, pickle, sys, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r6/c5')
from common5 import *
def load_e7(q):
    d = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r6/c5/e7_q%d.pkl' % q, 'rb'))
    return np.array(d['simple']), np.array(d['roots'], dtype=np.int64)
class W:
    def __init__(self, q):
        self.q = q; self.G = Geo(q); self.simple, self.roots = load_e7(q)
        self.code_tab = -np.ones(q ** 7, dtype=np.int64)
        pw = q ** np.arange(7)
        self.pw = pw
        self.code_tab[(self.G.C * pw).sum(1)] = np.arange(self.G.N)
        self.cache = {}
    def refl_perm(self, v):
        """permutation of points under x -> x - B(x,v) v"""
        key = tuple(int(t) for t in v)
        if key in self.cache: return self.cache[key]
        q = self.q; v = np.asarray(v, dtype=np.int64)
        C = self.G.C
        Y = C - ((C @ A7 @ v) % q)[:, None] * v[None, :]
        Y %= q
        # normalize
        first = np.argmax(Y != 0, axis=1)
        lead = Y[np.arange(len(Y)), first]
        inv = np.array([0] + [pow(int(a), q - 2, q) for a in range(1, q)])
        Y = (Y * inv[lead][:, None]) % q
        perm = self.code_tab[(Y * self.pw).sum(1)]
        assert (perm >= 0).all()
        self.cache[key] = perm
        return perm
    def roots_index(self, vs):
        return [self.refl_perm(v) for v in vs]
    def dynkin(self, edges, n, seed=0, tries=50):
        """find roots b_0..b_{n-1} with Gram = Cartan of graph (edges) mod q (randomised DFS); returns (n,7) array"""
        q = self.q; R = self.roots
        adjset = set(map(tuple, edges)) | set((b, a) for a, b in edges)
        rng = random.Random(seed)
        BR = (R @ A7 @ R.T) % q
        target = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            target[i, i] = 2 % q
            for j in range(n):
                if i != j:
                    target[i, j] = (-1 if (i, j) in adjset else 0) % q
        nodes = [0]
        def dfs(chosen):
            k = len(chosen)
            if k == n: return list(chosen)
            cand = np.ones(len(R), dtype=bool)
            for j, c in enumerate(chosen):
                cand &= (BR[c] == target[j, k])
            idx = np.nonzero(cand)[0].tolist()
            rng.shuffle(idx)
            for c in idx:
                if c in chosen: continue
                res = dfs(chosen + [c])
                if res is not None: return res
            return None
        for t in range(tries):
            c0 = rng.randrange(len(R))
            res = dfs([c0])
            if res is not None: return R[np.array(res)]
        return None
