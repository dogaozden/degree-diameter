# c8: maximum independent set of A u B for two independent sets A, B (conflict graph is bipartite between A and B).
# MIS = |A|+|B| - (maximum matching in the A-B conflict graph) by Konig's theorem.
import sys
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c8')
import orth as O

def load_flags(path):
    pid2i = {int(O.pid[i]): i for i in range(O.N)}
    out = []
    with open(path) as f:
        for line in f:
            p, l = map(int, line.split())
            out.append(pid2i[p])
    return sorted(set(out))

def max_matching(adj, nL, nR):
    matchR = [-1] * nR
    def try_(u, seen):
        for v in adj[u]:
            if seen[v]: continue
            seen[v] = True
            if matchR[v] == -1 or try_(matchR[v], seen):
                matchR[v] = u
                return True
        return False
    m = 0
    for u in range(nL):
        if try_(u, [False] * nR): m += 1
    return m

if __name__ == '__main__':
    A = load_flags(sys.argv[1]); B = load_flags(sys.argv[2])
    print("sizes", len(A), len(B), "indep A", O.is_indep(A), "indep B", O.is_indep(B), "overlap", len(set(A) & set(B)))
    C = (O.Bm(O.U[A], O.U[B]) == 0)
    adj = [list(np.nonzero(C[i])[0]) for i in range(len(A))]
    nu = max_matching(adj, len(A), len(B))
    print("conflict edges", int(C.sum()), "matching", nu, "=> MIS of union", len(A) + len(B) - nu)
