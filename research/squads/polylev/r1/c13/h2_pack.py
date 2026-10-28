"""Exact test: is there a set of K pairwise disjoint lines of H(2)? (budget search: at most 63 - 3K points left uncovered)
Usage: python3 h2_pack.py K"""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/polylev/r1/c13')
from h2_build import LP, PL, N


def packing(K):
    budget0 = N - 3 * K
    cover_of = [[i for i in range(N) if p in LP[i]] for p in range(N)]
    chosen = []
    nodes = [0]

    def rec(p, used, budget):
        nodes[0] += 1
        while p < N and (used >> p) & 1:
            p += 1
        if len(chosen) == K:
            return list(chosen)
        if p >= N:
            return None
        for i in cover_of[p]:
            m = sum(1 << x for x in LP[i])
            if used & m:
                continue
            chosen.append(i)
            r = rec(p + 1, used | m, budget)
            if r is not None:
                return r
            chosen.pop()
        if budget > 0:                      # point p stays uncovered
            return rec(p + 1, used | (1 << p), budget - 1)
        return None

    sol = rec(0, 0, budget0)
    return sol, nodes[0]


if __name__ == '__main__':
    K = int(sys.argv[1])
    sol, nodes = packing(K)
    print(f'K={K} pairwise disjoint lines: {"FOUND " + str(sorted(sol)) if sol else "none"} (nodes {nodes})')
