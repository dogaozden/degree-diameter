# Structure of the spread-restricted model for W(q): checks and data loading.
import sys, os, itertools
import numpy as np
D = '/home/user/degree-diameter/research/theorems/d5relax/data'
def load(q):
    pre = os.path.join(D, 'W%d' % q)
    adj = [list(map(int, l.split()[1:])) for l in open(pre + '_adj.txt').read().strip().split('\n')[1:]]
    L = [list(map(int, s.split())) for s in open(pre + '_lines.txt').read().strip().split('\n')[1:]]
    sp = list(map(int, open(pre + '_spread.txt').read().split()))
    return adj, L, sp
if __name__ == '__main__':
    q = int(sys.argv[1]); adj, L, sp = load(q); n = len(adj)
    S = q * q + 1
    lines_of_spread = [[p for p in range(n) if sp[p] == s] for s in range(S)]
    print('n', n, 'lines', len(L), 'spread lines', S, 'sizes', set(len(x) for x in lines_of_spread), 'line sizes', set(map(len, L)))
    # spread lines must be lines of W
    Lset = set(frozenset(l) for l in L)
    print('spread lines are lines:', all(frozenset(x) in Lset for x in lines_of_spread))
    # bijection check: for spread lines s != t, each point of s collinear with exactly one point of t
    C = np.zeros((n, n), dtype=int)
    for v in range(n):
        for u in adj[v]: C[v, u] = 1
    ok = True; cnt = 0
    for s in range(S):
        for t in range(S):
            if s == t: continue
            A = np.array(lines_of_spread[s]); B = np.array(lines_of_spread[t])
            M = C[np.ix_(A, B)]
            if not ((M.sum(1) == 1).all() and (M.sum(0) == 1).all()): ok = False
            cnt += 1
    print('bijection between all spread-line pairs:', ok, cnt)
    # each non-spread line: points on distinct spread lines
    spset = set(frozenset(x) for x in lines_of_spread)
    nonsp = [l for l in L if frozenset(l) not in spset]
    print('non-spread lines', len(nonsp), 'points on distinct spread lines:', all(len(set(sp[p] for p in l)) == len(l) for l in nonsp))
    # points per spread line through the lines count
    print('lines per point', np.bincount(np.bincount([p for l in L for p in l], minlength=n)).tolist())
