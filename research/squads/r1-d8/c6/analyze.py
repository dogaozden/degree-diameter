"""Classify unreached lift targets from one source: by vertex type (point/line) and base distance d(src,y)."""
import collections, sys
def load_base(path):
    with open(path) as fh:
        NB, M1, M2, E = map(int, fh.readline().split())
        adj = [[] for _ in range(NB)]
        for _ in range(E):
            u, v, a, b = map(int, fh.readline().split())
            adj[u].append((v, a % M1, b % M2)); adj[v].append((u, (-a) % M1, (-b) % M2))
    return NB, M1, M2, adj
def run(path, srcs, N):
    NB, M1, M2, adj = load_base(path)
    M = M1 * M2
    # base distances from each source
    for src in srcs:
        bd = [-1] * NB; bd[src] = 0; dq = collections.deque([src])
        while dq:
            v = dq.popleft()
            for (u, a, b) in adj[v]:
                if bd[u] < 0: bd[u] = bd[v] + 1; dq.append(u)
        dist = {(src, 0): 0}; fr = [(src, 0)]; lev = 0
        while fr and lev < 8:
            lev += 1; nf = []
            for (v, g) in fr:
                for (u, a, b) in adj[v]:
                    h = ((g // M2 + a) % M1) * M2 + (g % M2 + b) % M2
                    if (u, h) not in dist:
                        dist[(u, h)] = lev; nf.append((u, h))
            fr = nf
        cnt = collections.Counter()
        for v in range(NB):
            for g in range(M):
                if (v, g) not in dist:
                    cnt[('pt' if v < N else 'ln', bd[v])] += 1
        print(f'src {src} ({"pt" if src < N else "ln"}): unreached {sum(cnt.values())} by (type, base dist): {dict(sorted(cnt.items()))}', flush=True)
if __name__ == '__main__':
    run(sys.argv[1], [int(s) for s in sys.argv[2].split(',')], int(sys.argv[3]))
