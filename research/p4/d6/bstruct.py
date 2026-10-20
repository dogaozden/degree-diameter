"""Blocks of the Hermitian-spread unital and which q blocks through v the perfect whisker packings leave empty."""
import collections, itertools, random, sys
from hexbin import load


def unital(q, seed):
    q_, N, lines, crd = load(q)
    S = [int(x) for x in open(f'runs/S_q{q}_s{seed}.txt')]
    spt = {int(p): s for s in S for p in lines[s]}
    thr = collections.defaultdict(list)
    for k, L in enumerate(lines):
        for p in L:
            thr[int(p)].append(k)

    def sl(k):
        for p in lines[k]:
            if int(p) in spt:
                return spt[int(p)]
    blocks = set()
    for r in range(N):
        if r not in spt:
            blocks.add(frozenset(sl(k) for k in thr[r]))
    return S, lines, spt, sl, blocks


if __name__ == '__main__':
    q = 5
    S, lines, spt, sl, blocks = unital(q, 1)
    v = S[0]
    W = [int(x) for x in open('graphs/h5_whisk600_W.txt')]
    A = set(sl(w) for w in W)
    B = set(S) - A
    thru = [b for b in blocks if v in b]
    inB = [b for b in thru if b <= B]
    print('blocks through v in B:', len(inB))
    other = [b for b in blocks if v not in b]

    def inv(sel):
        U = set().union(*sel)
        return tuple(sorted(collections.Counter(len(b & U) for b in other).items()))
    print('found:', inv(inB))
    random.seed(0)
    cnt = collections.Counter(inv(random.sample(thru, q)) for _ in range(300))
    for k, c in cnt.most_common(12):
        print(c, k)
