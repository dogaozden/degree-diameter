"""Enumerate connected k-regular bipartite multigraph bases on r + r vertices (r x r nonnegative integer matrices with
row and column sums k), up to row/column permutations and transposition.  Writes base files "r" + edge lines.
usage: python3 bases.py k r outdir"""
import itertools, sys, os
def mats(k, r):
    rows = [x for x in itertools.product(range(k + 1), repeat=r) if sum(x) == k]
    out = []
    def rec(prefix, colsum):
        if len(prefix) == r:
            if all(c == k for c in colsum): out.append(tuple(prefix))
            return
        for x in rows:
            cs = [a + b for a, b in zip(colsum, x)]
            if max(cs) <= k: rec(prefix + [x], cs)
    rec([], [0] * r)
    return out
def canon(M):
    r = len(M); best = None
    for p in itertools.permutations(range(r)):
        for qq in itertools.permutations(range(r)):
            for t in (0, 1):
                N = tuple(tuple((M[p[i]][qq[j]] if not t else M[qq[j]][p[i]]) for j in range(r)) for i in range(r))
                if best is None or N < best: best = N
    return best
def connected(M):
    r = len(M); seen = {('a', 0)}; st = [('a', 0)]
    while st:
        s, i = st.pop()
        for j in range(r):
            w = M[i][j] if s == 'a' else M[j][i]
            nb = ('b', j) if s == 'a' else ('a', j)
            if w and nb not in seen: seen.add(nb); st.append(nb)
    return len(seen) == 2 * r
if __name__ == '__main__':
    k, r, outdir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; os.makedirs(outdir, exist_ok=True)
    cs = sorted({canon(M) for M in mats(k, r) if connected(M)})
    for idx, M in enumerate(cs):
        with open(f'{outdir}/k{k}r{r}_{idx:03d}.txt', 'w') as f:
            f.write(f'{r}\n')
            for i in range(r):
                for j in range(r):
                    for _ in range(M[i][j]): f.write(f'{i} {j}\n')
    print(k, r, len(cs), 'bases')
