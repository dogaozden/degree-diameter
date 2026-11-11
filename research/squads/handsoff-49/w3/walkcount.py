# count non-backtracking walks of length L (even <= 8 for same side, odd <= 9 for cross) from a root to each target
import collections, sys
L_ = open('w3base.txt').read().split()
n, m = int(L_[0]), int(L_[1])
E = [(int(L_[2+2*i]), int(L_[3+2*i])) for i in range(m)]
adj = collections.defaultdict(list)
for u, v in E: adj[u].append(v); adj[v].append(u)
def counts(root, Lmax):
    # walks[L][w] = number of NB walks of length L from root to w
    res = {}
    # state: (current vertex, previous vertex)
    cur = collections.Counter({(root, -1): 1})
    tot = collections.Counter()
    for L in range(1, Lmax + 1):
        nxt = collections.Counter()
        for (x, p), c in cur.items():
            for y in adj[x]:
                if y != p: nxt[(y, x)] += c
        cur = nxt
        per = collections.Counter()
        for (x, p), c in cur.items(): per[x] += c
        res[L] = per
    return res
for root in [0, 40]:
    res = counts(root, 9)
    same = collections.Counter(); cross = collections.Counter()
    for w in range(80):
        if (w < 40) == (root < 40):
            s = sum(res[L][w] for L in (2, 4, 6, 8))
            same[(w == root, s)] += 1
        else:
            s = sum(res[L][w] for L in (1, 3, 5, 7, 9))
            cross[s] += 1
    print('root', root, 'same-side (self-flag, walks<=8 even) histogram:', sorted(same.items()))
    print('   cross-side (walks<=9 odd) histogram:', sorted(cross.items()))
    # walks split by distance class
    dist_counts = collections.defaultdict(list)
    for w in range(80):
        if (w < 40) == (root < 40):
            s = sum(res[L][w] for L in (2, 4, 6, 8))
            dist_counts[s].append(w)
    print('   same-side walk totals:', {k: len(v) for k, v in sorted(dist_counts.items())})
