"""Enumerate connected 4-regular bipartite multigraph bases on k + k vertices (k x k nonnegative integer matrices with
row and column sums 4), up to row/column permutations and transposition.  Writes base files for mlift."""
import itertools, sys, os
def mats(k):
    rows = [r for r in itertools.product(range(5), repeat=k) if sum(r) == 4]
    out = []
    def rec(prefix, colsum):
        if len(prefix) == k:
            if all(c == 4 for c in colsum): out.append(tuple(prefix))
            return
        for r in rows:
            cs = [a + b for a, b in zip(colsum, r)]
            if max(cs) <= 4: rec(prefix + [r], cs)
    rec([], [0] * k)
    return out
def canon(M):
    k = len(M); best = None
    for p in itertools.permutations(range(k)):
        for qq in itertools.permutations(range(k)):
            for t in (0, 1):
                N = tuple(tuple((M[p[i]][qq[j]] if not t else M[qq[j]][p[i]]) for j in range(k)) for i in range(k))
                if best is None or N < best: best = N
    return best
def connected(M):
    k = len(M); seen = {('a', 0)}; st = [('a', 0)]
    while st:
        s, i = st.pop()
        for j in range(k):
            w = M[i][j] if s == 'a' else M[j][i]
            nb = ('b', j) if s == 'a' else ('a', j)
            if w and nb not in seen: seen.add(nb); st.append(nb)
    return len(seen) == 2 * k
if __name__ == '__main__':
    k = int(sys.argv[1]); outdir = sys.argv[2]; os.makedirs(outdir, exist_ok=True)
    cs = sorted({canon(M) for M in mats(k) if connected(M)})
    for idx, M in enumerate(cs):
        with open(f'{outdir}/k{k}_{idx:03d}.txt', 'w') as f:
            f.write(f'{k}\n')
            for i in range(k):
                for j in range(k):
                    for _ in range(M[i][j]): f.write(f'{i} {j}\n')
        print(idx, M)
    print('count', len(cs), file=sys.stderr)
