# a06: multiplicity profile. For each B-element y of the Haar graph, count non-backtracking walks from A0 of length <= 7
# (odd) and of length 9 that end at (B, y). Shows how many elements are covered exactly once (fragile) and how many
# walks of length 9 reach each uncovered element.
import sys, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r2/a06')
from analyze import load_bin, read_sol
def mult(volt, N, T, maxlen):
    out = collections.Counter()  # (length) -> Counter over B-element
    cur = collections.Counter({(None, 0): 1})   # (last index, element of current vertex in A side=0)
    per_len = {}
    # track group element of the current vertex: start at A-vertex element 0 (identity)
    cur = collections.Counter({(None, 0): 1})
    for step in range(1, maxlen + 1):
        new = collections.Counter()
        for (last, x), c in cur.items():
            for i, g in enumerate(volt):
                if i == last: continue
                y = int(T[x, g]) if step % 2 == 1 else int(T[x, invg[g]])
                new[(i, y)] += c
        cur = new
        if step % 2 == 1:
            per_len[step] = collections.Counter()
            for (_, y), c in cur.items(): per_len[step][y] += c
    return per_len
if __name__ == '__main__':
    tab, sol, maxlen = sys.argv[1], sys.argv[2], int(sys.argv[3])
    N, T = load_bin(tab)
    invg = [int(next(j for j in range(N) if T[g, j] == 0)) for g in range(N)]
    volt, _ = read_sol(sol)
    pl = mult(volt, N, T, 9)
    cov7 = collections.Counter()
    for L in (1, 3, 5, 7):
        for y, c in pl[L].items(): cov7[y] += c
    once = sum(1 for y in range(N) if cov7[y] == 1)
    zero = [y for y in range(N) if cov7[y] == 0]
    print('elements (B-side) with walk-count<=7 = 0:', len(zero), ' = 1:', once, ' = 2:', sum(1 for y in range(N) if cov7[y] == 2))
    print('distribution of walk-count<=7 over elements:', sorted(collections.Counter(cov7[y] for y in range(N)).items())[:8])
    for y in zero:
        print('uncovered y', y, 'quotient', y // 1, 'walks of length 9 reaching it:', pl[9][y])
