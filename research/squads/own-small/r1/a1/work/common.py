import numpy as np
G = "/home/user/degree-diameter/research/squads/own-small/seeds/groups/g220_2.txt"
def load_group():
    tok = open(G).read().split()
    N = int(tok[1]); assert tok[0] == "G" and int(tok[2]) == 2
    M = np.array(list(map(int, tok[4:4 + N * N])), dtype=np.int64).reshape(N, N)
    return N, M
def inverses(N, M):
    return [int(np.where(M[g] == 0)[0][0]) for g in range(N)]
def closure(M, gens):
    H = {0}; fr = [0]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = int(M[x, g])
                if y not in H: H.add(y); nf.append(y)
        fr = nf
    return frozenset(H)
def base_edges(path):
    b = open(path).read().split(); k, E = int(b[0]), int(b[1])
    return k, [(int(b[2 + 2 * e]), int(b[3 + 2 * e])) for e in range(E)]
