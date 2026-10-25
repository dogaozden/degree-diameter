# c2: exact maximum clique (Tomita-style greedy colouring bound) for small/medium dense-or-sparse graphs.
import numpy as np, sys, time
def max_clique(A, time_limit=600.0, lb=0):
    n = A.shape[0]
    adj = [set(np.nonzero(A[i])[0].tolist()) for i in range(n)]
    best = [[]]; best_size = [lb]; t0 = time.time(); nodes = [0]
    def color_sort(P):
        # greedy colouring of candidate list P; returns vertices and colour bounds in order
        order = []; bounds = []; uncol = set(P); k = 0
        while uncol:
            k += 1; Q = set(uncol)
            while Q:
                v = min(Q); Q.discard(v); Q -= adj[v]; uncol.discard(v)
                order.append(v); bounds.append(k)
        return order, bounds
    def expand(R, P):
        nodes[0] += 1
        if time.time() - t0 > time_limit: return
        order, bounds = color_sort(P)
        for i in range(len(order) - 1, -1, -1):
            if len(R) + bounds[i] <= best_size[0]: return
            v = order[i]
            R2 = R + [v]; P2 = P & adj[v]
            if not P2:
                if len(R2) > best_size[0]:
                    best_size[0] = len(R2); best[0] = R2[:]
            else:
                expand(R2, P2)
            P = P - {v}
    expand([], set(range(n)))
    return best[0], best_size[0], time.time() - t0 < time_limit, nodes[0]
if __name__ == '__main__':
    A = np.load(sys.argv[1]) if sys.argv[1].endswith('.npy') else None
    cl, sz, complete, nodes = max_clique(A)
    print('clique', sz, 'complete', complete, 'nodes', nodes)
