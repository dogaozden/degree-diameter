"""All connected cubic bipartite multigraphs with n+n vertices (biadjacency n x n, row/col sums 3), up to row and
column permutations and transposition (swapping the colours), as base files for lx / lanneal / lscreen.
A spanning tree (BFS from white 0) gets identity voltages ('= e').  Usage: python3 basegen.py n OUTDIR [--simple]"""
import itertools, os, sys
n, outdir = int(sys.argv[1]), sys.argv[2]
simple = '--simple' in sys.argv
rows = [r for r in itertools.product(range(4), repeat=n) if sum(r) == 3 and (not simple or max(r) <= 1)]
def canon(M):
    best = None
    for T in (M, tuple(zip(*M))):
        for p in itertools.permutations(range(n)):
            P = [T[i] for i in p]
            # sort columns lexicographically after row permutation (columns can be permuted freely)
            cols = sorted(zip(*P))
            key = tuple(zip(*cols))
            if best is None or key < best:
                best = key
    return best
def connected(M):
    seen, st = {('w', 0)}, [('w', 0)]
    while st:
        s, i = st.pop()
        for j in range(n):
            a = M[i][j] if s == 'w' else M[j][i]
            if a:
                t = ('b', j) if s == 'w' else ('w', j)
                if t not in seen:
                    seen.add(t); st.append(t)
    return len(seen) == 2 * n
found = set()
def rec(prefix, colsum):
    if len(prefix) == n:
        if all(c == 3 for c in colsum) and connected(prefix):
            found.add(canon(tuple(prefix)))
        return
    for r in rows:
        if prefix and r < prefix[-1]:
            continue            # rows in non-decreasing order (row permutations)
        cs = [colsum[j] + r[j] for j in range(n)]
        if max(cs) <= 3:
            rec(prefix + [r], cs)
rec([], [0] * n)
os.makedirs(outdir, exist_ok=True)
for idx, M in enumerate(sorted(found)):
    # edges: white i -> vertex i, black j -> vertex n + j; BFS tree from white 0 gets identity voltages
    edges = [(i, n + j) for i in range(n) for j in range(n) for _ in range(M[i][j])]
    tree, seen, st = set(), {0}, [0]
    while st:
        v = st.pop(0)
        for ei, (a, b) in enumerate(edges):
            if ei in tree: continue
            for x, y in ((a, b), (b, a)):
                if x == v and y not in seen:
                    seen.add(y); tree.add(ei); st.append(y)
    girth_hint = 'simple' if max(max(r) for r in M) <= 1 else 'multi'
    with open(os.path.join(outdir, f'b{n}{n}{"s" if simple else ""}_{idx}.txt'), 'w') as f:
        f.write(f'# {n}+{n} cubic base ({girth_hint}), biadjacency {M}; gauge tree fixed to e\n{2 * n}\n')
        for ei, (a, b) in enumerate(edges):
            f.write(f'{a} {b}' + (' = e' if ei in tree else '') + '\n')
print(f'{len(found)} connected {n}+{n} cubic bipartite {"simple graphs" if simple else "multigraphs"}')
