"""All connected cubic bipartite multigraphs with p white + p black vertices, up to isomorphism (row/column
permutations and transposition of the biadjacency matrix).  Usage: python3 enum_bases.py p OUTDIR
Writes OUTDIR/b<p>_<i>.txt in liftx base format (whites 0..p-1, blacks p..2p-1)."""
import itertools, os, sys

def rows(p, s=3):
    if p == 1:
        yield (s,); return
    for a in range(s, -1, -1):
        for r in rows(p - 1, s - a):
            yield (a,) + r

def connected(M, p):
    seen, st = {0}, [0]
    while st:
        x = st.pop()
        nb = [p + j for j in range(p) if M[x][j]] if x < p else [i for i in range(p) if M[i][x - p]]
        for y in nb:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == 2 * p

def canon(M, p):
    best = None
    for T in (M, tuple(zip(*M))):
        for cp in itertools.permutations(range(p)):
            R = sorted((tuple(row[c] for c in cp) for row in T), reverse=True)
            key = tuple(R)
            if best is None or key > best: best = key
    return best

def main():
    p, out = int(sys.argv[1]), sys.argv[2]
    os.makedirs(out, exist_ok=True)
    R = list(rows(p))
    found = set()
    def rec(M, colsum, start):
        if len(M) == p:
            if all(c == 3 for c in colsum) and connected(M, p):
                found.add(canon(tuple(M), p))
            return
        for i in range(start, len(R)):
            r = R[i]
            if all(colsum[j] + r[j] <= 3 for j in range(p)):
                rec(M + [r], [colsum[j] + r[j] for j in range(p)], i)
    rec([], [0] * p, 0)
    for i, M in enumerate(sorted(found, reverse=True)):
        E = [(a, p + b) for a in range(p) for b in range(p) for _ in range(M[a][b])]
        with open(os.path.join(out, f"b{p}_{i}.txt"), "w") as f:
            f.write(f"{2 * p} {len(E)}\n" + "".join(f"{u} {v}\n" for u, v in E))
    print(p, len(found))

main()
