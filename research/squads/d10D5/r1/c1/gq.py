"""gq.py: W(q) geometry from a gq bin file (research/d10D7/gqgen.c format) and small helpers for the hub work."""
import struct, random, sys

def load(fn):
    with open(fn, 'rb') as f:
        q, N, L = struct.unpack('3i', f.read(12)); Q1 = q + 1
        lines = [list(struct.unpack(f'{Q1}i', f.read(4 * Q1))) for _ in range(L)]
    lof = [[] for _ in range(N)]
    for l, ps in enumerate(lines):
        for p in ps: lof[p].append(l)
    return q, N, lines, lof

def perp(lines, lof, p):
    """points collinear with p (including p)"""
    s = set()
    for l in lof[p]: s.update(lines[l])
    return s

def lperp(lines, lof, l):
    """lines concurrent with l (including l)"""
    s = set()
    for p in lines[l]: s.update(lof[p])
    return s

def find_spread(lines, N, seed=0, limit=10 ** 6):
    """exact cover of the points by lines (Algorithm X with the fewest-candidates rule)"""
    rng = random.Random(seed)
    X = {p: set() for p in range(N)}
    for l, ps in enumerate(lines):
        for p in ps: X[p].add(l)
    Y = {l: ps for l, ps in enumerate(lines)}
    sol = []; cnt = [0]
    def select(r):
        cols = []
        for j in Y[r]:
            for i in X[j]:
                for k in Y[i]:
                    if k != j: X[k].remove(i)
            cols.append(X.pop(j))
        return cols
    def deselect(r, cols):
        for j in reversed(Y[r]):
            X[j] = cols.pop()
            for i in X[j]:
                for k in Y[i]:
                    if k != j: X[k].add(i)
    def solve():
        if not X: return True
        cnt[0] += 1
        if cnt[0] > limit: return False
        c = min(X, key=lambda c: (len(X[c]), rng.random()))
        cand = list(X[c]); rng.shuffle(cand)
        for r in cand:
            sol.append(r); cols = select(r)
            if solve(): return True
            deselect(r, cols); sol.pop()
        return False
    return sorted(sol) if solve() else None

if __name__ == '__main__':
    q, N, lines, lof = load(sys.argv[1])
    s = find_spread(lines, N, seed=int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    print(len(s) if s else None, s)
