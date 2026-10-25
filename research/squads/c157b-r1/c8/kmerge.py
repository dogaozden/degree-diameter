#!/usr/bin/env python3
"""kmerge.py: exact maximum independent set of the union of two independent point sets A and S2 of H(11).
The union's collinearity graph is bipartite (A\\S2 versus S2\\A; common points are isolated), so its MIS is
|A| + |B| - nu, nu = maximum matching between B = S2\\A and A (Konig). Used for conjugates h(RH) under SL(3,11)."""
import sys, os, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r1/shared')
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r1/c8')
from geom import load, pl_table
from collections import deque

N, L, LP, C = load()
PL = pl_table(N, L, LP)


def owner_lines(S):
    own = np.full(L, -1, dtype=np.int64)
    S = np.asarray(S, dtype=np.int64)
    own[PL[S].reshape(-1)] = np.repeat(S, 12)
    return own


def max_matching(adj, nB, nA):
    """Hopcroft-Karp. adj[b] = list of a-indices. returns matchB (b->a or -1), matchA (a->b or -1)."""
    INF = 1 << 30
    matchB = [-1] * nB; matchA = [-1] * nA
    for b in range(nB):                       # greedy start
        for a in adj[b]:
            if matchA[a] < 0:
                matchA[a] = b; matchB[b] = a; break
    while True:
        dist = [INF] * nB
        dq = deque()
        for b in range(nB):
            if matchB[b] < 0:
                dist[b] = 0; dq.append(b)
        found = False
        while dq:
            b = dq.popleft()
            for a in adj[b]:
                b2 = matchA[a]
                if b2 < 0:
                    found = True
                elif dist[b2] == INF:
                    dist[b2] = dist[b] + 1; dq.append(b2)
        if not found:
            break
        # iterative DFS along layers
        it = [0] * nB
        for root in range(nB):
            if matchB[root] >= 0:
                continue
            stack = [root]; path_a = []
            while stack:
                b = stack[-1]
                advanced = False
                while it[b] < len(adj[b]):
                    a = adj[b][it[b]]; it[b] += 1
                    b2 = matchA[a]
                    if b2 < 0:
                        # augment along stack
                        path_a.append(a)
                        for k in range(len(stack)):
                            bb = stack[k]; aa = path_a[k]
                            matchB[bb] = aa; matchA[aa] = bb
                        stack = []; advanced = True
                        break
                    if dist[b2] == dist[b] + 1:
                        path_a.append(a); stack.append(b2); advanced = True
                        break
                if not advanced:
                    dist[b] = INF; stack.pop()
                    if path_a: path_a.pop()
    return matchB, matchA


def merge(RH, S2, verbose=False):
    """returns (set of ids of a maximum independent set of RH u S2, gain over |RH|)"""
    RH = np.asarray(RH, dtype=np.int64); S2 = np.asarray(S2, dtype=np.int64)
    inR = np.zeros(N, bool); inR[RH] = True
    inS = np.zeros(N, bool); inS[S2] = True
    common = np.nonzero(inR & inS)[0]
    A = np.nonzero(inR & ~inS)[0]; B = np.nonzero(inS & ~inR)[0]
    aidx = np.full(N, -1, dtype=np.int64); aidx[A] = np.arange(len(A))
    own = owner_lines(RH)
    adj = []
    for b in B:
        nb = own[PL[b]]
        nb = nb[nb >= 0]
        # owners of lines through b in RH are never in common (both sets independent)
        a_list = [int(aidx[p]) for p in nb if aidx[p] >= 0]
        if len(a_list) != len(nb):
            raise ValueError('owner outside A: input sets not independent')
        adj.append(a_list)
    mB, mA = max_matching(adj, len(B), len(A))
    nu = sum(1 for x in mB if x >= 0)
    # Konig cover: Z = reachable from unmatched A-side (X = A) by alternating paths
    Zx = [False] * len(A); Zy = [False] * len(B)
    dq = deque([a for a in range(len(A)) if mA[a] < 0])
    for a in dq: Zx[a] = True
    adjA = [[] for _ in range(len(A))]
    for b, al in enumerate(adj):
        for a in al: adjA[a].append(b)
    while dq:
        a = dq.popleft()
        for b in adjA[a]:
            if not Zy[b] and mB[b] != a:
                Zy[b] = True
                a2 = mB[b]
                if a2 >= 0 and not Zx[a2]:
                    Zx[a2] = True; dq.append(a2)
    keepA = [A[a] for a in range(len(A)) if Zx[a]]          # A minus cover: cover = (A \ Z) | (B & Z)
    keepB = [B[b] for b in range(len(B)) if not Zy[b]]
    res = np.concatenate([common, np.array(keepA, dtype=np.int64), np.array(keepB, dtype=np.int64)])
    res = np.sort(res)
    # the Konig cover must be a vertex cover; the kept set must be independent
    tmp = np.zeros(N, bool); tmp[res] = True
    bad = int((tmp[LP].sum(1) > 1).sum())          # lines carrying two chosen points
    if bad:
        raise RuntimeError('merged set not independent (%d)' % bad)
    gain = len(res) - len(RH)
    if verbose:
        print('|RH|=%d |S2|=%d common=%d |B|=%d nu=%d -> %d (gain %d)' % (len(RH), len(S2), len(common), len(B), nu, len(res), gain), flush=True)
    return res, gain


def read_ids(fn):
    return np.array([int(x) for x in open(fn) if x.strip() and not x.startswith('#')], dtype=np.int64)


if __name__ == '__main__':
    RH = read_ids(sys.argv[1]); S2 = read_ids(sys.argv[2])
    res, gain = merge(RH, S2, verbose=True)
    if len(sys.argv) > 3:
        with open(sys.argv[3], 'w') as f:
            f.write('\n'.join(map(str, res.tolist())) + '\n')
