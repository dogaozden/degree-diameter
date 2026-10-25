#!/usr/bin/env python3
"""bimerge.py GRAPH OUT SOL1 SOL2 [SOL3 ...]: exact best independent set inside the union of two independent sets.
The union of two independent sets induces a bipartite graph (S1 \\ S2 versus S2 \\ S1, the common vertices isolated), so
its maximum independent set is the complement of a minimum vertex cover, computed from a maximum matching (Konig).
Tries every pair of the given solutions and writes the largest result. GRAPH: og_*.txt ("M E", "idx rep deg nbrs...")."""
import sys
sys.setrecursionlimit(10000)


def load(g):
    with open(g) as f:
        M, E = map(int, f.readline().split())
        nb = [None] * M
        for line in f:
            a = list(map(int, line.split()))
            nb[a[0]] = set(a[3:3 + a[2]])
    return nb


def readsol(fn):
    return [int(l) for l in open(fn) if l.strip() and not l.startswith('#')]


def merge(nb, s1, s2):
    S1, S2 = set(s1), set(s2)
    common = S1 & S2
    A = sorted(S1 - S2)
    B = sorted(S2 - S1)
    Bset = set(B)
    adj = {a: [b for b in nb[a] if b in Bset] for a in A}
    match_b = {}

    def aug(a, seen):
        for b in adj[a]:
            if b in seen:
                continue
            seen.add(b)
            if b not in match_b or aug(match_b[b], seen):
                match_b[b] = a
                return True
        return False
    for a in A:
        aug(a, set())
    match_a = {a: b for b, a in match_b.items()}
    # Konig: Z = vertices reachable from unmatched A by alternating paths; cover = (A \ Z) | (B & Z)
    Z = set()
    stack = [a for a in A if a not in match_a]
    Z.update(stack)
    while stack:
        a = stack.pop()
        for b in adj[a]:
            if b not in Z:
                Z.add(b)
                a2 = match_b.get(b)
                if a2 is not None and a2 not in Z:
                    Z.add(a2)
                    stack.append(a2)
    cover = set(a for a in A if a not in Z) | set(b for b in B if b in Z)
    ind = common | (set(A) | set(B)) - cover
    for v in ind:
        assert not (nb[v] & ind)
    return sorted(ind)


def main():
    g, out = sys.argv[1], sys.argv[2]
    nb = load(g)
    sols = [(fn, readsol(fn)) for fn in sys.argv[3:]]
    best = max(sols, key=lambda t: len(t[1]))
    bestset, bestname = best[1], best[0]
    for i in range(len(sols)):
        for j in range(i + 1, len(sols)):
            r = merge(nb, sols[i][1], sols[j][1])
            print('%s + %s: %d + %d -> %d (common %d)' % (sols[i][0], sols[j][0], len(sols[i][1]), len(sols[j][1]), len(r), len(set(sols[i][1]) & set(sols[j][1]))))
            if len(r) > len(bestset):
                bestset, bestname = r, sols[i][0] + '+' + sols[j][0]
    with open(out, 'w') as f:
        f.write('# bimerge best %d from %s\n' % (len(bestset), bestname))
        f.write('\n'.join(map(str, bestset)) + '\n')
    print('best', len(bestset), bestname)


if __name__ == '__main__':
    main()
