# Non-backtracking walk counts on the 6-vertex base of the path-split lift (card c5).
# Blocks: 0=A0 1=A1 2=A2 (side A), 3=B0 4=B1 5=B2 (side B). Edges: internal A0-B0, A2-B0, A1-B1, A1-B2;
# external A0-B1 (a), A0-B2 (5-a), A2-B1 (5-a), A2-B2 (a), A1-B0 (4).
import sys
from collections import defaultdict

def base_edges(a):
    E = [(0, 3, 'int'), (2, 3, 'int'), (1, 4, 'int'), (1, 5, 'int')]
    E += [(0, 4, 'ext')] * a + [(0, 5, 'ext')] * (5 - a) + [(2, 4, 'ext')] * (5 - a) + [(2, 5, 'ext')] * a + [(1, 3, 'ext')] * 4
    return E

def walk_counts(a, Lmax=5):
    E = base_edges(a)
    darts = []  # (tail, head, edge index)
    for idx, (u, v, _) in enumerate(E):
        darts.append((u, v, idx))
        darts.append((v, u, idx))
    out = defaultdict(list)
    for d in darts:
        out[d[0]].append(d)
    res = {}
    for src in range(6):
        # cur[dart] = number of NB walks from src of current length ending with that dart
        cur = defaultdict(int)
        ends = defaultdict(int)  # ends[(L, vertex)]
        ends[(0, src)] = 1
        for d in out[src]:
            cur[d] += 1
        for L in range(1, Lmax + 1):
            for d, c in cur.items():
                ends[(L, d[1])] += c
            if L == Lmax:
                break
            nxt = defaultdict(int)
            for d, c in cur.items():
                for e in out[d[1]]:
                    if e[2] == d[2]:  # backtrack along the same edge
                        continue
                    nxt[e] += c
            cur = nxt
        res[src] = ends
    return res

if __name__ == '__main__':
    names = ['A0', 'A1', 'A2', 'B0', 'B1', 'B2']
    side = [0, 0, 0, 1, 1, 1]
    for a in [1, 2, 3]:
        W = walk_counts(a)
        print('a=%d' % a)
        worst_same = None
        worst_opp = None
        for src in range(6):
            line = []
            for T in range(6):
                if side[T] == side[src]:
                    cnt = sum(W[src].get((L, T), 0) for L in (0, 2, 4))
                    line.append('%s:%d' % (names[T], cnt))
                    if worst_same is None or cnt < worst_same[0]:
                        worst_same = (cnt, names[src], names[T])
                else:
                    cnt = sum(W[src].get((L, T), 0) for L in (1, 3, 5))
                    line.append('%s:%d(opp)' % (names[T], cnt))
                    if worst_opp is None or cnt < worst_opp[0]:
                        worst_opp = (cnt, names[src], names[T])
            print('  from %s  %s' % (names[src], '  '.join(line)))
        print('  min same-side walks (len<=4): %d from %s to %s  => need m <= this' % worst_same)
        print('  min opposite-side walks (len<=5): %d from %s to %s' % worst_opp)
