# a06: per-coset counting view. For a voltage set (group indices g_i with quotient labels j_i = g_i // M in Z_K),
# count non-backtracking walks of odd length <= 7 from A0 to B-vertices, grouped by quotient coset; compare with
# the number of distinct covered elements per coset (from the actual group table) and with |M|.
import sys, struct, collections
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r2/a06')
from analyze import load_bin, read_sol, haar_adj, bfs

def walk_counts(volt, M, K, maxlen=7):
    q = [v // M for v in volt]
    m = len(volt)
    # state: (last index, label) ; B-endpoints after odd steps
    cur = collections.Counter({(None, 0): 1})
    W = collections.Counter()
    for step in range(1, maxlen + 1):
        new = collections.Counter()
        for (last, lab), c in cur.items():
            for i in range(m):
                if i == last:
                    continue
                nl = (lab + q[i]) % K if step % 2 == 1 else (lab - q[i]) % K
                new[(i, nl)] += c
        cur = new
        if step % 2 == 1:
            for (_, lab), c in cur.items():
                W[lab] += c
    return W

if __name__ == '__main__':
    tab, sol, M, K = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    N, T = load_bin(tab)
    volt, _ = read_sol(sol)
    adj = haar_adj(N, T, volt)
    dA = bfs(adj, 0)
    W = walk_counts(volt, M, K)
    cov = collections.Counter(); unc = collections.Counter()
    for y in range(N):
        if dA[N + y] <= 8: cov[y // M] += 1
        else: unc[y // M] += 1
    print('volt quotients', [v // M for v in volt], 'walks(len<=7) total', sum(W.values()))
    for j in range(K):
        print('coset %2d  walks %4d  |M| %d  covered %3d  uncovered %d  bound %d' % (j, W[j], M, cov[j], unc[j], max(0, M - W[j])))
